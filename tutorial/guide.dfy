// The answers to the exercises in Dafny tutorial on
// https://rise4fun.com/Dafny/tutorial/guide

/***************************/
/* Pre- and Postconditions */
/***************************/

// Exercise 0
method Max(a: int, b:int) returns (c: int)
  // What postcondition should go here, so that the function operates as expected?
  // Hint: there are many ways to write this.
  ensures a <= c && b <= c
  ensures a < b ==> c == b
  ensures a >= b ==> c == a
{
  // fill in the code here
  if a < b {
    return b;
  } else {
    return a;
  }
}

/***************************/
/*       Assertions        */
/***************************/

// Exercise 1
method Testing() {
  // Assert some things about Max. Does it operate as you expect?
  // If it does not, can you think of a way to fix it?
  var test1 := Max(2, 3);
  assert test1 == 3;
  var test2 := Max(3, 2);
  assert test2 == 3;
}

// Exercise 2
method Abs(x: int) returns (y: int)
   // Add a precondition here.
   requires x < 0
   ensures 0 <= y
   ensures 0 <= x ==> x == y
   ensures x < 0 ==> y == -x
{
   // Simplify the body to just one return statement
   return -x;
}

// Exercise 3
method Abs_Ex3_1(x: int) returns (y: int)
   // Add a precondition here so that the method verifies.
   // Don't change the postconditions.
   requires x == -1
   ensures 0 <= y
   ensures 0 <= x ==> x == y
   ensures x < 0 ==> y == -x
{
  y:= x + 2;
}
method Abs3_Ex3_2(x: int) returns (y: int)
   // Add a precondition here so that the method verifies.
   // Don't change the postconditions.
   // The Error is: arguments must have comparable types (got int and real)
   // requires x == -0.5
   ensures 0 <= y
   ensures 0 <= x ==> x == y
   ensures x < 0 ==> y == -x
{
  y:= x + 1;
}

/***************************/
/*       Assertions        */
/***************************/

// Exercise 4
function max(a: int, b: int): int {
  // Fill in an expression here.
  if a < b then b else a
}

method Testing_Ex4() {
  // Add assertions to check max here.
  assert max(2, 3) == 3;
  assert max(3, 2) == 3;
}

// Exercise 5
method Testing_Ex5() {
  // Add assertions to check max here. Be sure to capture it to a local variable
  // Don't know why there is not a error...
  var test1 := max(2, 3);
  assert test1 == 3;
}

// Exercise 6
function abs(x: int): int {
  if 0 <= x then x else -x
}
method Abs_Ex6(x: int) returns (y: int)
  // Use abs here, then confirm the method still verifies.
  ensures y == abs(x)
{
   // Then change this body to also use abs.
   if x < 0
     { return -x; }
   else
     { return x; }
}

/***************************/
/*    Loop Invariants      */
/***************************/

// Exercise 7
method m(n: nat)
{
   var i: int := 0;
   while i < n
      // The loop still verify.
      invariant 0 <= i <= n + 2  // Change this. What happens?
   {
      i := i + 1;
   }
   // The assertion will fail.
   assert i == n;
}

// Exercise 8
method m_Ex8(n: nat)
{
   var i: int := 0;
   // The loop and assertion still verifies
   //  because the verification is based on the loop invariant.
   while i != n  // Change this. What happens?
      invariant 0 <= i <= n
   {
      i := i + 1;
   }
   assert i == n;
}

// Exercise 9
function fib(n: nat): nat
{
   if n == 0 then 0 else
   if n == 1 then 1 else
                  fib(n - 1) + fib(n - 2)
}
method ComputeFib_ex9(n: nat) returns (b: nat)
   ensures b == fib(n)  // Do not change this postcondition
{
   // Change the method body to instead use c as described.
   // You will need to change both the initialization and the loop.
   var i: int := 0;
       b := 0;
   var c := 1;
   while i < n
      invariant 0 <= i <= n
      invariant b == fib(i)
      invariant c == fib(i + 1)
   {
      b, c := c, b + c;
      i := i + 1;
   }
}

// Exercise 10
method ComputeFib_Ex10(n: nat) returns (b: nat)
   ensures b == fib(n)
{
   var i: int := 0;
   var a := 1;
       b := 0;
   while i < n
      // Fill in the invariants here.
      invariant 0 <= i <= n
      invariant  b == fib(i)
      invariant if i == 0 then a == 1 else a == fib(i-1)
   {
      a, b := b, a + b;
      i := i + 1;
   }
}

/***************************/
/*      Termination        */
/***************************/

// Exercise 11
method m_Ex11()
{
   var i, n := 0, 20;
   while i != n
      // Error: cannot prove termination; try supplying a decreases clause for the loop
      //        decreases if i <= n then n - i else i - n
      // decreases n - i
   {
      i := i + 1;
   }
}

/***************************/
/*      Quantifiers        */
/***************************/

// Exercise 12
method FindMax(a: array<int>) returns (i: int)
   // Annotate this method with pre- and postconditions
   // that ensure it behaves as described.
   requires a.Length > 0
   ensures 0 <= i < a.Length
   ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[i]
{
   // Fill in the body that calculates the INDEX of the maximum.
   i := 0;
   var index := 0;
   while index < a.Length
      invariant 0 <= index <= a.Length
      invariant 0 <= i < a.Length
      invariant forall k :: 0 <= k < index ==> a[k] <= a[i]
   {
     if a[index] > a[i] {
       i := index;
     }
     index := index + 1;
   }
}

/***************************/
/*         Framing         */
/***************************/

// Exercise 13
predicate sorted(a: array<int>)
   requires a != null
   reads a
{
   // Fill in a new body here.
   forall j, k :: 0 <= j < k < a.Length ==> a[j] < a[k]
}

// Exercise 14
predicate sorted_Ex14(a: array<int>)
   // It seems that the new version of Dafny has separated the optional type.
   // Therefore, remove the `a != null` won't have any effect.
   reads a
{
   // Fill in a new body here.
   forall j, k :: 0 <= j < k < a.Length ==> a[j] < a[k]
}

/***************************/
/*      Binary Search      */
/***************************/

// Exercise 15
method BinarySearch(a: array<int>, value: int) returns (index: int)
   requires a != null && 0 <= a.Length && sorted(a)
   ensures 0 <= index ==> index < a.Length && a[index] == value
   ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value
{
   var low, high := 0, a.Length;
   while low < high
      invariant 0 <= low <= high <= a.Length
      invariant forall i ::
         0 <= i < a.Length && !(low <= i < high) ==> a[i] != value
   {
      var mid := (low + high) / 2;
      if a[mid] < value
      {
         // Change to `low := mid` will cause no termination.
         low := mid + 1;
      }
      else if value < a[mid]
      {
         // Change to `high := mid + 1` will fail the invariant `low <= high`.
         high := mid;
      }
      else
      {
         return mid;
      }
   }
   return -1;
}
