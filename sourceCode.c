#include <stdio.h>
#include <iostream>
#include <cmath>
#include <stdlib.h>

using namespace std;


bool lu(double* a, int* pivot, int n)//矩阵LU分解
{
      int i,j,k;
      double max,temp;
      max = 0;
      temp = 0;
      for (i=0; i<n-1; i++)//依次对第i列进行处理
	  {
	  	    // 选出i列的主元,记录主元位置
	  	    max = fabs(a[n*i + i]);
	  	   	pivot[i]=i;
  		    for(j=i+1; j<n; j++)//j表示第j行
  		    {
    		   if( fabs(a[n*j + i])>max)
			   {
   				   max=  fabs(a[n*j + i]) ;
   				   pivot[i]=j;
   			   }
            }
            // 对第i列进行行变换，使得主元在对角线上
			if(pivot[i]!=i)
			{
				for(j=i; j<n; j++)//ij与pivot[i]j换 只用对上三角进行处理
				{
				    temp=a[n*i + j];
				    a[n*i + j]=a[n*pivot[i]+ j];
				    a[n*pivot[i]+ j]=temp;
				}
			}
			for(j=i+1; j<n; j++)//Pi 部分下三角L
			    	a[n*j + i]=a[n*j+i]/a[n*i+i];
			for(j=i+1; j<n; j++)//计算上三角U
				for(k=i+1; k<n; k++)
			    	a[n*j + k]=a[n*j+k]- a[n*j+i]*a[n*i+k];
 	  }
      //计算下三角 L
	  for(i=0; i<n-2; i++)//i行k列
	    	for(k=i+1; k<n-1;k++)
	    	{
	    		    temp=a[n*pivot[k] + i];
				    a[n*pivot[k] + i]=a[k*n + i];
				    a[k*n + i]=temp;
	    	}

      return false ;
}
bool guass(double const* lu, int const* p, double* b, int n)//求线性代数方程组的解
{
      int i,j;
      double temp;
	  //按qivot对b行变换，与LU匹配
	  for(i=0; i<n-1; i++)  //貌似错误在这里哦
	  {
			temp = b[p[i]];
		    b[p[i]] = b[i];
			b[i]=temp;
  	  }
  	  //Ly=b,将y的内容放入b
  	  for(i=0; i<n; i++)
	  	    for(j=0; j<i; j++)
		      	b[i]=b[i]-lu[n*i+j]*b[j];

	  //Uy=x,将x的内容放入b

	  for(i=n-1; i>=0; i--)
	  {
  		    for(j=n-1; j>i; j--)
		        b[i]=b[i]-lu[n*i+j]*b[j];

	        b[i]=b[i]/lu[n*i+i];

  	  }
      return false;
}
void qr(double* a, double* d, int n) //矩阵的QR分解
{
	  int i,j,l,k;


      double tem,m;
      double *temp;
      temp = (double *)malloc(sizeof(double)*n);
      for (i=0; i<n-1; i++)//依次对第i列进行处理
	  {
	  	    //获得tem值
	  	    m = 0 ;
  		    for(j=i; j<n; j++)//j表示第j行
  		       m = m +a[n*j + i]*a[n*j + i ];
    		if(a[n*i + i ]>0)
			     m = -sqrt(m);
	        else
	             m = sqrt(m);
           //获得temp放入矩阵，并存主元d
            tem = 0 ;
            d[i] = m ;
            a[n*i +i] = a[n*i +i] - m;
            for(j=i; j<=n-1; j++)
                tem=tem + a[n*j +i]*a[n*j +i];
			tem= sqrt(tem);
			for(j=i; j<=n-1; j++)
			    a[n*j +i] = a[n*j +i]/tem ;
            // 调整矩阵
			 for(k=i+1;k<n;k++)
			 {
 			    for(j=i; j<n; j++)
			    {
			    	tem = 0 ;
    				for(l=i; l<n; l++)
    				     tem =tem + a[n*j + i]*a[n*l + i]*a[n*l + k];
			        temp[j] = a[j*n+k] - 2*tem;
    			}
    			for(j=i; j<n; j++)
				      a[j*n+k] = temp[j];
 			 }
       }
       d[n-1] = a[(n-1)*n+n-1];
}
bool householder(double const*qr, double const*d, double*b, int n)//求线性代数方程组的解
{
    int i,j,l;
	double rem;
	double *temp;
	temp = (double *)malloc(sizeof(double)*n);

	for(i=0; i<n-1; i++)
	{
		for(j=i; j<n; j++)
		{
			rem = 0;
			for(l=i;l<n; l++)
				rem = rem + qr[l*n+i]*qr[j*n+i]*b[l];
			temp[j] = b[j] - 2*rem;
		}
		for(j=i; j<n; j++)
			b[j] = temp[j];
	}

	for(j=n-1; j>-1; j--)
	{
		for(l=n-1; l!=j;--l)
			b[j] =b[j] - b[l]*qr[j*n+l];
		b[j]  =	b[j] /d[j];
	}

	return false;
}

double GetNorm(double* a,int n){
	double y=0;
	for(int i=0;i<n;i++){
	y+=a[i]*a[i];
	}
	return sqrt(y);

}

void diyiti_lu(int num){
    int n=num;
	double hilbert[n*n];
	int pivot[n];
	double b[n];

		//H方阵
	for(int i=0;i<n;i++){
		for(int j =0;j<n;j++){
			hilbert[i*n+j]=1.0/(i+1+j+1-1);
			}
	}
	//H方阵的b
	for(int k=0;k<n;k++){
	 for(int p=0;p<n;p++){
		b[k]+=hilbert[k*n+p];
		}
	}

	//H矩阵LU分解
	lu(hilbert,pivot,n);
	//高斯求解线性方程组
	guass(hilbert,pivot,b,n);

	printf("高斯消去法线性方程组的解为:");
	for(int l=0;l<n;l++){
	printf(" %lf",b[l]);
	}
	printf("\n");
	printf("主元的位置排列为:");
	for(int l=0;l<n-1;l++){
	printf(" %d",pivot[l]);
	}
	printf("\n");

	for(int i=0;i<n;i++){
	b[i]=b[i]-1;
	}
	double norm = GetNorm(b,n);
	cout << "n="<<n<<"时，理论与数值解的差的二范数为"<<norm << endl;


}
void diyiti_qr(int num){
    int n=num;
	double hilbert[n*n];
	int pivot[n+1];
	double b[n];
	double d[n];
	for(int i=0;i<n;i++)
        d[i]=0;
		//H方阵
	for(int i=0;i<n;i++){
		for(int j =0;j<n;j++){
			hilbert[i*n+j]=1.0/(i+1+j+1-1);
			}
	}
	//H方阵的b
	for(int k=0;k<n;k++){
	 for(int p=0;p<n;p++){
		b[k]+=hilbert[k*n+p];
		}
	}
	qr(hilbert,d,n);
	householder(hilbert,d,b,n);
	printf("Householder method的解为:");
	for(int l=0;l<n;l++){
	printf(" %lf",b[l]);
	}
	printf("\n");

	for(int i=0;i<n;i++){
	b[i]=b[i]-1;
	}
	double norm = GetNorm(b,n);
	cout << "n="<<n<<"时，理论与数值解的差的二范数为"<<norm << endl;

}
void dierti_lu(int num){
    int n=num;
	double hilbert[n*n];
	int pivot[n];
	double b[n];

		//H方阵
	for(int i=0;i<n;i++){
		for(int j =0;j<n;j++){
                if(j<i){
                hilbert[i*n+j]=-1;
                }else if(j==i){
                hilbert[i*n+j]=1;
                }else{
                    if(j==n-1){
                    hilbert[i*n+j]=1;
                    }else{
                    hilbert[i*n+j]=0;
                    }
                }

			}
	}
	//H方阵的b
	for(int k=0;k<n;k++){
	 for(int p=0;p<n;p++){
		b[k]+=hilbert[k*n+p];
		}
	}

	//H矩阵LU分解
	lu(hilbert,pivot,n);
	//高斯求解线性方程组
	guass(hilbert,pivot,b,n);

	printf("高斯消去法线性方程组的解为:\n");
	for(int l=0;l<n;l++){
		
	printf(" %lf",b[l]);
	if((l+1)%5==0) printf("\n");
	}
	printf("\n");
	printf("主元的位置排列为:");
	for(int l=0;l<n-1;l++){
	printf(" %d",pivot[l]);
	}
	printf("\n");

	for(int i=0;i<n;i++){
	b[i]=b[i]-1;
	}
	double norm = GetNorm(b,n);
	cout << "n="<<n<<"时，理论与数值解的差的二范数为"<<norm << endl;


}

void dierti_qr(int num){
    int n=num;
	double hilbert[n*n];
	int pivot[n+1];
	double b[n];
	double d[n];
	for(int i=0;i<n;i++)
        d[i]=0;
		//H方阵
		for(int i=0;i<n;i++){
		for(int j =0;j<n;j++){
                if(j<i){
                hilbert[i*n+j]=-1;
                }else if(j==i){
                hilbert[i*n+j]=1;
                }else{
                    if(j==n-1){
                    hilbert[i*n+j]=1;
                    }else{
                    hilbert[i*n+j]=0;
                    }
                }

			}
	}
	//H方阵的b
	for(int k=0;k<n;k++){
	 for(int p=0;p<n;p++){
		b[k]+=hilbert[k*n+p];
		}
	}
	qr(hilbert,d,n);
	householder(hilbert,d,b,n);
	printf("Householder method的解为:\n");
	for(int l=0;l<n;l++){
	printf(" %lf",b[l]);
		if((l+1)%5==0) printf("\n");
	}
	printf("\n");

	for(int i=0;i<n;i++){
	b[i]=b[i]-1;
	}
	double norm = GetNorm(b,n);
	cout << "n="<<n<<"时，理论与数值解的差的二范数为"<<norm << endl;

}
void disanti_lu(int num){
    int n=num;
	double hilbert[n*n];
	int pivot[n];
	double b[n];

		//H方阵
	for(int i=0;i<n;i++){
		for(int j =0;j<n;j++){
                if(j<i){
                hilbert[i*n+j]=-1;
                }else if(j==i){
                hilbert[i*n+j]=1;
                }else{
                    if(j==n-1){
                    hilbert[i*n+j]=1;
                    }else{
                    hilbert[i*n+j]=0;
                    }
                }

			}
	}
	//H方阵的b
	for(int k=0;k<n;k++){
        if(k==n-1)
            b[k]=n;
        else
            b[k]=k+2;
	}

	//H矩阵LU分解
	lu(hilbert,pivot,n);
	//高斯求解线性方程组
	guass(hilbert,pivot,b,n);

	printf("高斯消去法线性方程组的解为:\n");
	for(int l=0;l<n;l++){
	printf(" %lf",b[l]);
		if((l+1)%5==0) printf("\n");
	}
	printf("\n");
	printf("主元的位置排列为:");
	for(int l=0;l<n-1;l++){
	printf(" %d",pivot[l]);
	}
	printf("\n");

	for(int i=0;i<n;i++){
	b[i]=b[i];
	}
	double norm = GetNorm(b,n);
	cout << "n="<<n<<"时，数值解残量的二范数为"<<norm << endl;


}

void disanti_qr(int num){
 int n=num;
	double hilbert[n*n];
	int pivot[n+1];
	double b[n];
	double d[n];
	for(int i=0;i<n;i++)
        d[i]=0;
		//H方阵
		for(int i=0;i<n;i++){
		for(int j =0;j<n;j++){
                if(j<i){
                hilbert[i*n+j]=-1;
                }else if(j==i){
                hilbert[i*n+j]=1;
                }else{
                    if(j==n-1){
                    hilbert[i*n+j]=1;
                    }else{
                    hilbert[i*n+j]=0;
                    }
                }

			}
	}
	//H方阵的b
    for(int k=0;k<n;k++){
        if(k==n-1)
            b[k]=n;
        else
            b[k]=k+2;
	}
	qr(hilbert,d,n);
	householder(hilbert,d,b,n);
	printf("Householder method的解为:\n");
	for(int l=0;l<n;l++){
	printf(" %lf",b[l]);
		if((l+1)%5==0) printf("\n");
	}
	printf("\n");

	for(int i=0;i<n;i++){
	b[i]=b[i];
	}
	double norm = GetNorm(b,n);
	cout << "n="<<n<<"时，数值解的残量的二范数为"<<norm << endl;
}
int main()
{

//diyiti_lu(10);
//diyiti_lu(10);
dierti_qr(50);
//diyiti_qr(10);
//dierti_qr(150);
//disanti_qr(100);

	return 0;
}
