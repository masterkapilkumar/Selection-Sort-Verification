predicate perm(A:seq<int>, B:seq<int>)
{
	multiset(A) == multiset(B)
}

predicate partOrdered(A:array<int>, a:int, b:int)
	requires 0 <= a <= b <= A.Length
	reads A
{
	forall i,j :: a <= i < j < b ==> A[i] <= A[j]
}

predicate ordered(A:array<int>)
	reads A
{
	partOrdered(A, 0, A.Length)
}

method selectionSort (A:array<int>)
	modifies A
	ensures ordered(A)                          //the final array is sorted
	ensures perm (A[..], old(A[..]))            //the array does not change its contents
{
	if A.Length > 1
	{
		var i, j := 0, 0;
		var min_idx := i;
		while i < A.Length
		invariant 0 <= i <= A.Length
		invariant 0 <= min_idx < A.Length
		invariant perm (A[..], old(A[..]))          //the array does not change its contents
		invariant forall k, l :: 0 <= k < i <= l < A.Length ==> A[k] <= A[l]        //every element in the left part of the array is smaller than any element in right part
		invariant partOrdered(A, 0, i)              //the array is partially sorted (left part)
		{
			j := i + 1;
			min_idx := i;
			while j < A.Length
			invariant 1 <= j <= A.Length
			invariant i <= min_idx < A.Length
			invariant perm (A[..], old(A[..]))              //the array does not change its contents
			invariant forall k :: i <= k < j ==> A[k] >= A[min_idx]
			{
				if A[j] < A[min_idx]
				{
					min_idx := j;
				}
				j := j + 1;
			}
			A[i], A[min_idx] := A[min_idx], A[i];
			i := i + 1;
		}
	}
}

method Main() {
	var A := new int[10];
	A[0],A[1],A[2],A[3],A[4],A[5],A[6],A[7],A[8],A[9] := 4,8,8,3,5,10,9,9,4,7;
	print "A = ", A[..], "\n";
	selectionSort(A);
	print "A = ", A[..], "\n";
}