// Copyright (c) 2007 Intel Corp.

// Black-Scholes
// Analytical method for calculating European Options
//
//
// Reference Source: Options, Futures, and Other Derivatives, 3rd Edition, Prentice
// Hall, John C. Hull,
#include <stdint.h>

#include <time.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>

double myGetime() {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC_RAW, &t);
  return (double)t.tv_sec + (double)(t.tv_nsec / 1000000000.0);
}

unsigned long read_cycles(){
  unsigned long cycles, lo, hi;
   __asm__ __volatile__ ("rdtsc" : "=a" (lo), "=d" (hi));
   cycles = ((uint64_t)hi << 32) | lo;
 return cycles;
}

double t[10];
unsigned long s[2],e[2];

#ifdef ENABLE_PARSEC_HOOKS
#include <hooks.h>
#endif

// Multi-threaded pthreads header
#ifdef ENABLE_THREADS
// Add the following line so that icc 9.0 is compatible with pthread lib.
#define __thread __threadp
MAIN_ENV
#undef __thread
#endif

// Multi-threaded OpenMP header
#ifdef ENABLE_OPENMP
#include <omp.h>
#endif

#ifdef ENABLE_TBB
#include "tbb/blocked_range.h"
#include "tbb/parallel_for.h"
#include "tbb/task_scheduler_init.h"
#include "tbb/tick_count.h"

using namespace std;
using namespace tbb;
#endif //ENABLE_TBB

// Multi-threaded header for Windows
#ifdef WIN32
#pragma warning(disable : 4305)
#pragma warning(disable : 4244)
#include <windows.h>
#endif

//Precision to use for calculations
#define fptype float

#define NUM_RUNS 100

typedef struct OptionData_ {
        fptype s;          // spot price
        fptype strike;     // strike price
        fptype r;          // risk-free interest rate
        fptype divq;       // dividend rate
        fptype v;          // volatility
        fptype t;          // time to maturity or option expiration in years
                           //     (1yr = 1.0, 6mos = 0.5, 3mos = 0.25, ..., etc)
        char OptionType;   // Option type.  "P"=PUT, "C"=CALL
        fptype divs;       // dividend vals (not used in this test)
        fptype DGrefval;   // DerivaGem Reference Value
} OptionData;

OptionData *data;
fptype *prices;
int numOptions;

int    * otype;
fptype * sptprice;
fptype * strike;
fptype * rate;
fptype * volatility;
fptype * otime;
int numError = 0;
int nThreads;

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
// Cumulative Normal Distribution Function
// See Hull, Section 11.8, P.243-244
#define inv_sqrt_2xPI 0.39894228040143270286

fptype CNDF ( fptype InputX )
{
    //s[1] = read_cycles();

    int sign;

    fptype OutputX;
    fptype xInput;
    fptype xNPrimeofX;
    fptype expValues;
    fptype xK2;
    fptype xK2_2, xK2_3;
    fptype xK2_4, xK2_5;
    fptype xLocal, xLocal_1;
    fptype xLocal_2, xLocal_3;

    // Check for negative value of InputX
    if (InputX < 0.0) {
        InputX = -InputX;
        sign = 1;
    } else
        sign = 0;

    xInput = InputX;

    // Compute NPrimeX term common to both four & six decimal accuracy calcs
    expValues = exp(-0.5f * InputX * InputX);
    xNPrimeofX = expValues;
    xNPrimeofX = xNPrimeofX * inv_sqrt_2xPI;

    xK2 = 0.2316419 * xInput;
    xK2 = 1.0 + xK2;
    xK2 = 1.0 / xK2;
    xK2_2 = xK2 * xK2;
    xK2_3 = xK2_2 * xK2;
    xK2_4 = xK2_3 * xK2;
    xK2_5 = xK2_4 * xK2;

    xLocal_1 = xK2 * 0.319381530;
    xLocal_2 = xK2_2 * (-0.356563782);
    xLocal_3 = xK2_3 * 1.781477937;
    xLocal_2 = xLocal_2 + xLocal_3;
    xLocal_3 = xK2_4 * (-1.821255978);
    xLocal_2 = xLocal_2 + xLocal_3;
    xLocal_3 = xK2_5 * 1.330274429;
    xLocal_2 = xLocal_2 + xLocal_3;

    xLocal_1 = xLocal_2 + xLocal_1;
    xLocal   = xLocal_1 * xNPrimeofX;
    xLocal   = 1.0 - xLocal;

    OutputX  = xLocal;

    if (sign) {
        OutputX = 1.0 - OutputX;
    }

    //e[1] =  read_cycles();

    return OutputX;
}

//////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////
inline fptype BlkSchlsEqEuroNoDiv( fptype sptprice,
                            fptype strike, fptype rate, fptype volatility,
                            fptype time, int otype, float timet )
{
    //s[0] =  read_cycles();

    fptype OptionPrice;

    // local private working variables for the calculation
    fptype xStockPrice;
    fptype xStrikePrice;
    fptype xRiskFreeRate;
    fptype xVolatility;
    fptype xTime;
    fptype xSqrtTime;

    fptype logValues;
    fptype xLogTerm;
    fptype xD1;
    fptype xD2;
    fptype xPowerTerm;
    fptype xDen;
    fptype d1;
    fptype d2;
    fptype FutureValueX;
    fptype NofXd1;
    fptype NofXd2;
    fptype NegNofXd1;
    fptype NegNofXd2;

    xStockPrice = sptprice;
    xStrikePrice = strike;
    xRiskFreeRate = rate;
    xVolatility = volatility;

    xTime = time;
    xSqrtTime = sqrt(xTime);

    logValues = log( sptprice / strike );

    xLogTerm = logValues;


    xPowerTerm = xVolatility * xVolatility;
    xPowerTerm = xPowerTerm * 0.5;

    xD1 = xRiskFreeRate + xPowerTerm;
    xD1 = xD1 * xTime;
    xD1 = xD1 + xLogTerm;

    xDen = xVolatility * xSqrtTime;
    xD1 = xD1 / xDen;
    xD2 = xD1 -  xDen;

    d1 = xD1;
    d2 = xD2;

    //NofXd1 = CNDF( d1 );
    //NofXd2 = CNDF( d2 );

    fptype q2 = sqrt(2);
    fptype t1 = -d1/q2;
    fptype t2 = -d2/q2;
    NofXd1 = erfc(t1);
    NofXd2 = erfc(t2);
    NofXd1 = NofXd1/2;
    NofXd2 = NofXd2/2;

    FutureValueX = strike * ( exp( -(rate)*(time) ) );
    if (otype == 0) {
        OptionPrice = (sptprice * NofXd1) - (FutureValueX * NofXd2);
    } else {
        NegNofXd1 = (1.0 - NofXd1);
        NegNofXd2 = (1.0 - NofXd2);
        OptionPrice = (FutureValueX * NegNofXd2) - (sptprice * NegNofXd1);
    }

    //e[0] = read_cycles();
    return OptionPrice;
}

inline fptype BlkSchlsEqEuroNoDiv2(float S, float X, float r, float v, float T, int Call, int na)
{
      float d1, d2;

      d1=(logf(S)-logf(X)+(r+v*v/(float)2)*T)/(v*sqrtf(T));
      d2=d1-v*sqrtf(T);

      if(!Call)
          return S * erfcf(-d1/sqrtf(2))/2-X * expf(-r*T)*erfcf(-d2/sqrtf(2))/2;
      else
          return X * expf(-r * T) * erfcf(d2/sqrtf(2))/2 - S * erfcf(d1/sqrtf(2))/2;

}

#ifdef ENABLE_TBB
struct mainWork {
  mainWork() {}
  mainWork(mainWork &w, tbb::split) {}

  void operator()(const tbb::blocked_range<int> &range) const {
    fptype price;
    int begin = range.begin();
    int end = range.end();

    for (int i=begin; i!=end; i++) {
      /* Calling main function to calculate option value based on
       * Black & Scholes's equation.
       */

      price = BlkSchlsEqEuroNoDiv( sptprice[i], strike[i],
                                   rate[i], volatility[i], otime[i],
                                   otype[i], 0);
      prices[i] = price;

#ifdef ERR_CHK
      fptype priceDelta = data[i].DGrefval - price;
      if( fabs(priceDelta) >= 1e-5 ){
        fprintf(stderr,"Error on %d. Computed=%.5f, Ref=%.5f, Delta=%.5f\n",
               i, price, data[i].DGrefval, priceDelta);
        numError ++;
      }
#endif
    }
  }
};

#endif // ENABLE_TBB

//////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////

#ifdef ENABLE_TBB
int bs_thread(void *tid_ptr) {
    int j;
    tbb::affinity_partitioner a;

    mainWork doall;
    for (j=0; j<NUM_RUNS; j++) {
      tbb::parallel_for(tbb::blocked_range<int>(0, numOptions), doall, a);
    }

    return 0;
}
#else // !ENABLE_TBB

#ifdef WIN32
DWORD WINAPI bs_thread(LPVOID tid_ptr){
#else
int bs_thread(void *tid_ptr) {
#endif
    int i, j;
    register fptype price , price1, price2, price3;
    fptype priceDelta;
    int tid = *(int *)tid_ptr;
    int start = tid * (numOptions / nThreads);
    int end = start + (numOptions / nThreads);

    fptype xQ2 = M_SQRT1_2;

    t[0] = myGetime();
    for (j=0; j<NUM_RUNS; j++) {
#ifdef ENABLE_OPENMP
#pragma omp parallel for private(i, price, priceDelta)
        for (i=0; i<numOptions; i++) {
#else  //ENABLE_OPENMP
        for (i=start; i<end; i+=4) {
#endif //ENABLE_OPENMP
            /* Calling main function to calculate option value based on
             * Black & Scholes's equation.
             */
            //price = BlkSchlsEqEuroNoDiv( sptprice[i], strike[i], rate[i], volatility[i], otime[i], otype[i], 0);
            //prices[i] = price;


            /*
            price = BlkSchlsEqEuroNoDiv( sptprice[i], strike[i], rate[i], volatility[i], otime[i], otype[i], 0);
            price1 = BlkSchlsEqEuroNoDiv( sptprice[i+1], strike[i+1], rate[i+1], volatility[i+1], otime[i+1], otype[i+1], 0);
            price2 = BlkSchlsEqEuroNoDiv( sptprice[i+2], strike[i+2], rate[i+2], volatility[i+2], otime[i+2], otype[i+2], 0);
            price3 = BlkSchlsEqEuroNoDiv( sptprice[i+3], strike[i+3], rate[i+3], volatility[i+3], otime[i+3], otype[i+3], 0);
            prices[i] = price;
            prices[i+1] = price1;
            prices[i+2] = price2;
            prices[i+3] = price3;
            */


            register fptype OptionPrice;
            register fptype OptionPrice1;
            register fptype OptionPrice2;
            register fptype OptionPrice3;

            register fptype xStockPrice;
            register fptype xStockPrice1;
            register fptype xStockPrice2;
            register fptype xStockPrice3;

            register fptype xStrikePrice;
            register fptype xStrikePrice1;
            register fptype xStrikePrice2;
            register fptype xStrikePrice3;

            register fptype xRiskFreeRate;
            register fptype xRiskFreeRate1;
            register fptype xRiskFreeRate2;
            register fptype xRiskFreeRate3;

            register fptype xVolatility;
            register fptype xVolatility1;
            register fptype xVolatility2;
            register fptype xVolatility3;

            register fptype xTime;
            register fptype xTime1;
            register fptype xTime2;
            register fptype xTime3;

            register int xType ;
            register int xType1;
            register int xType2 ;
            register int xType3;

            fptype xSqrtTime;
            fptype xSqrtTime1;
            fptype xSqrtTime2;
            fptype xSqrtTime3;

            fptype xLogTerm;
            fptype xLogTerm1;
            fptype xLogTerm2;
            fptype xLogTerm3;

            fptype xD1;
            fptype xD1_1;
            fptype xD1_2;
            fptype xD1_3;

            fptype xD2;
            fptype xD2_1;
            fptype xD2_2;
            fptype xD2_3;

            fptype xPowerTerm;
            fptype xPowerTerm1;
            fptype xPowerTerm2;
            fptype xPowerTerm3;

            fptype xDen;
            fptype xDen1;
            fptype xDen2;
            fptype xDen3;

            fptype FutureValueX;
            fptype FutureValueX1;
            fptype FutureValueX2;
            fptype FutureValueX3;

            fptype NofXd1;
            fptype NofXd1_1;
            fptype NofXd1_2;
            fptype NofXd1_3;

            fptype NofXd2;
            fptype NofXd2_1;
            fptype NofXd2_2;
            fptype NofXd2_3;

            fptype NegNofXd1;
            fptype NegNofXd1_1;
            fptype NegNofXd1_2;
            fptype NegNofXd1_3;

            fptype NegNofXd2;
            fptype NegNofXd2_1;
            fptype NegNofXd2_2;
            fptype NegNofXd2_3;

            fptype XeTerm;
            fptype XeTerm1;
            fptype XeTerm2;
            fptype XeTerm3;

            xStockPrice = sptprice[i];
            xStockPrice1 = sptprice[i+1];
            xStockPrice2 = sptprice[i+2];
            xStockPrice3 = sptprice[i+3];

            xStrikePrice =  strike[i];
            xStrikePrice1 =  strike[i+1];
            xStrikePrice2 =  strike[i+2];
            xStrikePrice3 =  strike[i+3];

            xRiskFreeRate = rate[i];
            xRiskFreeRate1 = rate[i+1];
            xRiskFreeRate2 = rate[i+2];
            xRiskFreeRate3 = rate[i+3];

            xVolatility =  volatility[i];
            xVolatility1 =  volatility[i+1];
            xVolatility2 =  volatility[i+2];
            xVolatility3 =  volatility[i+3];

            xTime = otime[i];
            xTime1 = otime[i+1];
            xTime2 = otime[i+2];
            xTime3 = otime[i+3];

            xType = otype[i] ;
            xType1 = otype[i+1];
            xType2 = otype[i+2];
            xType3 = otype[i+3];

            xSqrtTime = sqrt(xTime);
            xSqrtTime1 = sqrt(xTime1);
            xSqrtTime2 = sqrt(xTime2);
            xSqrtTime3 = sqrt(xTime3);

            xLogTerm =  xStockPrice / xStrikePrice;
            xLogTerm1 = xStockPrice1 / xStrikePrice1;
            xLogTerm2 = xStockPrice2 / xStrikePrice2;
            xLogTerm3 = xStockPrice3 / xStrikePrice3;

            xLogTerm =   log( xLogTerm );
            xLogTerm1 =  log( xLogTerm1 );
            xLogTerm2 =  log( xLogTerm2 );
            xLogTerm3 =  log( xLogTerm3 );

            xPowerTerm = xVolatility * xVolatility;
            xPowerTerm1 = xVolatility1 * xVolatility1;
            xPowerTerm2 = xVolatility2 * xVolatility2;
            xPowerTerm3 = xVolatility3 * xVolatility3;

            xPowerTerm = xPowerTerm * 0.5;
            xPowerTerm1 = xPowerTerm1 * 0.5;
            xPowerTerm2 = xPowerTerm2 * 0.5;
            xPowerTerm3 = xPowerTerm3 * 0.5;

            xD1 = xRiskFreeRate + xPowerTerm;
            xD1_1 = xRiskFreeRate1 + xPowerTerm1;
            xD1_2 = xRiskFreeRate2 + xPowerTerm2;
            xD1_3 = xRiskFreeRate3 + xPowerTerm3;

            xD1 = xD1 * xTime;
            xD1_1 = xD1_1 * xTime1;
            xD1_2 = xD1_2 * xTime2;
            xD1_3 = xD1_3 * xTime3;

            xD1 = xD1 + xLogTerm;
            xD1_1 = xD1_1 + xLogTerm1;
            xD1_2 = xD1_2 + xLogTerm2;
            xD1_3 = xD1_3 + xLogTerm3;

            xDen = xVolatility * xSqrtTime;
            xDen1 = xVolatility1 * xSqrtTime1;
            xDen2 = xVolatility2 * xSqrtTime2;
            xDen3 = xVolatility3 * xSqrtTime3;

            xD1 = xD1 / xDen;
            xD1_1 = xD1_1 / xDen1;
            xD1_2 = xD1_2 / xDen2;
            xD1_3 = xD1_3 / xDen3;

            xD2 = xD1 -  xDen;
            xD2_1 = xD1_1 -  xDen1;
            xD2_2 = xD1_2 -  xDen2;
            xD2_3 = xD1_3 -  xDen3;

            NofXd1 = -xD1*xQ2;
            NofXd1_1 = -xD1_1*xQ2;
            NofXd1_2 = -xD1_2*xQ2;
            NofXd1_3 = -xD1_3*xQ2;

            NofXd2 = -xD2*xQ2;
            NofXd2_1 = -xD2_1*xQ2;
            NofXd2_2 = -xD2_2*xQ2;
            NofXd2_3 = -xD2_3*xQ2;

            NofXd1 = erfc(NofXd1);
            NofXd1_1 = erfc(NofXd1_1);
            NofXd1_2 = erfc(NofXd1_2);
            NofXd1_3 = erfc(NofXd1_3);

            NofXd2 = erfc(NofXd2);
            NofXd2_1 = erfc(NofXd2_1);
            NofXd2_2 = erfc(NofXd2_2);
            NofXd2_3 = erfc(NofXd2_3);


            NofXd1 = NofXd1*0.5;
            NofXd1_1 = NofXd1_1*0.5;
            NofXd1_2 = NofXd1_2*0.5;
            NofXd1_3 = NofXd1_3*0.5;


            NofXd2 = NofXd2*0.5;
            NofXd2_1 = NofXd2_1*0.5;
            NofXd2_2 = NofXd2_2*0.5;
            NofXd2_3 = NofXd2_3*0.5;

            XeTerm = exp( -(xRiskFreeRate)*(xTime) );
            XeTerm1 = exp( -(xRiskFreeRate1)*(xTime1) );
            XeTerm2 = exp( -(xRiskFreeRate2)*(xTime2) );
            XeTerm3 = exp( -(xRiskFreeRate3)*(xTime3) );

            FutureValueX = xStrikePrice * XeTerm;
            FutureValueX1 = xStrikePrice1 * XeTerm1;
            FutureValueX2 = xStrikePrice2 * XeTerm2;
            FutureValueX3 = xStrikePrice3 * XeTerm3;


            if (xType == 0) {
                OptionPrice = (xStockPrice * NofXd1) - (FutureValueX * NofXd2);
            } else {
                NegNofXd1 = (1.0 - NofXd1);
                NegNofXd2 = (1.0 - NofXd2);
                OptionPrice = (FutureValueX * NegNofXd2) - (xStockPrice * NegNofXd1);
            }

            if (xType1 == 0) {
                OptionPrice1 = (xStockPrice1 * NofXd1_1) - (FutureValueX1 * NofXd2_1);
            } else {
                NegNofXd1_1 = (1.0 - NofXd1_1);
                NegNofXd2_1 = (1.0 - NofXd2_1);
                OptionPrice1 = (FutureValueX1 * NegNofXd2_1) - (xStockPrice1 * NegNofXd1_1);
            }

            if (xType2 == 0) {
                OptionPrice2 = (xStockPrice2 * NofXd1_2) - (FutureValueX2 * NofXd2_2);
            } else {
                NegNofXd1_2 = (1.0 - NofXd1_2);
                NegNofXd2_2 = (1.0 - NofXd2_2);
                OptionPrice2 = (FutureValueX2 * NegNofXd2_2) - (xStockPrice2 * NegNofXd1_2);
            }

            if (xType3 == 0) {
                OptionPrice3 = (xStockPrice3 * NofXd1_3) - (FutureValueX3 * NofXd2_3);
            } else {
                NegNofXd1_3 = (1.0 - NofXd1_3);
                NegNofXd2_3 = (1.0 - NofXd2_3);
                OptionPrice3 = (FutureValueX3 * NegNofXd2_3) - (xStockPrice3 * NegNofXd1_3);
            }

            prices[i] = OptionPrice;
            prices[i+1] = OptionPrice1;
            prices[i+2] = OptionPrice2;
            prices[i+3] = OptionPrice3;


#ifdef ERR_CHK
            priceDelta = data[i].DGrefval - price;
            if( fabs(priceDelta) >= 1e-4 ){
                printf("Error on %d. Computed=%.5f, Ref=%.5f, Delta=%.5f\n",
                       i, price, data[i].DGrefval, priceDelta);
                numError ++;
            }
#endif
        }
    }
    t[1] = myGetime();
    printf("mytime %f\n",t[1]-t[0]);
    //printf("bs %lu\n",e[0]-s[0]);
    //printf("cd %lu\n",e[1]-s[1]);
    return 0;
}
#endif //ENABLE_TBB

int main (int argc, char **argv)
{
    FILE *file;
    int i;
    int loopnum;
    fptype * buffer;
    int * buffer2;
    int rv;

#ifdef PARSEC_VERSION
#define __PARSEC_STRING(x) #x
#define __PARSEC_XSTRING(x) __PARSEC_STRING(x)
        printf("PARSEC Benchmark Suite Version "__PARSEC_XSTRING(PARSEC_VERSION)"\n");
	fflush(NULL);
#else
        printf("PARSEC Benchmark Suite\n");
	fflush(NULL);
#endif //PARSEC_VERSION
#ifdef ENABLE_PARSEC_HOOKS
   __parsec_bench_begin(__parsec_blackscholes);
#endif

   if (argc != 4)
        {
                printf("Usage:\n\t%s <nthreads> <inputFile> <outputFile>\n", argv[0]);
                exit(1);
        }
    nThreads = atoi(argv[1]);
    char *inputFile = argv[2];
    char *outputFile = argv[3];

    //Read input data from file
    file = fopen(inputFile, "r");
    if(file == NULL) {
      printf("ERROR: Unable to open file `%s'.\n", inputFile);
      exit(1);
    }
    rv = fscanf(file, "%i", &numOptions);
    if(rv != 1) {
      printf("ERROR: Unable to read from file `%s'.\n", inputFile);
      fclose(file);
      exit(1);
    }
    if(nThreads > numOptions) {
      printf("WARNING: Not enough work, reducing number of threads to match number of options.\n");
      nThreads = numOptions;
    }

#if !defined(ENABLE_THREADS) && !defined(ENABLE_OPENMP) && !defined(ENABLE_TBB)
    if(nThreads != 1) {
        printf("Error: <nthreads> must be 1 (serial version)\n");
        exit(1);
    }
#endif

    // alloc spaces for the option data
    data = (OptionData*)malloc(numOptions*sizeof(OptionData));
    prices = (fptype*)malloc(numOptions*sizeof(fptype));
    for ( loopnum = 0; loopnum < numOptions; ++ loopnum )
    {
        rv = fscanf(file, "%f %f %f %f %f %f %c %f %f", &data[loopnum].s, &data[loopnum].strike, &data[loopnum].r, &data[loopnum].divq, &data[loopnum].v, &data[loopnum].t, &data[loopnum].OptionType, &data[loopnum].divs, &data[loopnum].DGrefval);
        if(rv != 9) {
          printf("ERROR: Unable to read from file `%s'.\n", inputFile);
          fclose(file);
          exit(1);
        }
    }
    rv = fclose(file);
    if(rv != 0) {
      printf("ERROR: Unable to close file `%s'.\n", inputFile);
      exit(1);
    }

#ifdef ENABLE_THREADS
    MAIN_INITENV(,8000000,nThreads);
#endif
    printf("Num of Options: %d\n", numOptions);
    printf("Num of Runs: %d\n", NUM_RUNS);

#define PAD 256
#define LINESIZE 64

    buffer = (fptype *) malloc(5 * numOptions * sizeof(fptype) + PAD);
    sptprice = (fptype *) (((unsigned long long)buffer + PAD) & ~(LINESIZE - 1));
    strike = sptprice + numOptions;
    rate = strike + numOptions;
    volatility = rate + numOptions;
    otime = volatility + numOptions;

    buffer2 = (int *) malloc(numOptions * sizeof(fptype) + PAD);
    otype = (int *) (((unsigned long long)buffer2 + PAD) & ~(LINESIZE - 1));

    for (i=0; i<numOptions; i++) {
        otype[i]      = (data[i].OptionType == 'P') ? 1 : 0;
        sptprice[i]   = data[i].s;
        strike[i]     = data[i].strike;
        rate[i]       = data[i].r;
        volatility[i] = data[i].v;
        otime[i]      = data[i].t;
    }

    printf("Size of data: %d\n", numOptions * (sizeof(OptionData) + sizeof(int)));

#ifdef ENABLE_PARSEC_HOOKS
    __parsec_roi_begin();
#endif

#ifdef ENABLE_THREADS
#ifdef WIN32
    HANDLE *threads;
    int *nums;
    threads = (HANDLE *) malloc (nThreads * sizeof(HANDLE));
    nums = (int *) malloc (nThreads * sizeof(int));

    for(i=0; i<nThreads; i++) {
        nums[i] = i;
        threads[i] = CreateThread(0, 0, bs_thread, &nums[i], 0, 0);
    }
    WaitForMultipleObjects(nThreads, threads, TRUE, INFINITE);
    free(threads);
    free(nums);
#else
    int *tids;
    tids = (int *) malloc (nThreads * sizeof(int));

    for(i=0; i<nThreads; i++) {
        tids[i]=i;
        CREATE_WITH_ARG(bs_thread, &tids[i]);
    }
    WAIT_FOR_END(nThreads);
    free(tids);
#endif //WIN32
#else //ENABLE_THREADS
#ifdef ENABLE_OPENMP
    {
        int tid=0;
        omp_set_num_threads(nThreads);
        bs_thread(&tid);
    }
#else //ENABLE_OPENMP
#ifdef ENABLE_TBB
    tbb::task_scheduler_init init(nThreads);

    int tid=0;
    bs_thread(&tid);
#else //ENABLE_TBB
    //serial version
    int tid=0;
    bs_thread(&tid);
#endif //ENABLE_TBB
#endif //ENABLE_OPENMP
#endif //ENABLE_THREADS

#ifdef ENABLE_PARSEC_HOOKS
    __parsec_roi_end();
#endif

    //Write prices to output file
    file = fopen(outputFile, "w");
    if(file == NULL) {
      printf("ERROR: Unable to open file `%s'.\n", outputFile);
      exit(1);
    }
    rv = fprintf(file, "%i\n", numOptions);
    if(rv < 0) {
      printf("ERROR: Unable to write to file `%s'.\n", outputFile);
      fclose(file);
      exit(1);
    }
    for(i=0; i<numOptions; i++) {
      rv = fprintf(file, "%.18f\n", prices[i]);
      if(rv < 0) {
        printf("ERROR: Unable to write to file `%s'.\n", outputFile);
        fclose(file);
        exit(1);
      }
    }
    rv = fclose(file);
    if(rv != 0) {
      printf("ERROR: Unable to close file `%s'.\n", outputFile);
      exit(1);
    }

#ifdef ERR_CHK
    printf("Num Errors: %d\n", numError);
#endif
    free(data);
    free(prices);

#ifdef ENABLE_PARSEC_HOOKS
    __parsec_bench_end();
#endif

    return 0;
}
