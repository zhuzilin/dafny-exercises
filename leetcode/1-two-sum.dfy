method TwoSum(nums: seq<int>, target: int) returns (res: seq<int>)
  requires |nums| >= 2
  // There will be one solution.
  requires exists i, j :: 0 <= i < j < |nums| && nums[i] + nums[j] == target
  // only one solution.
  requires forall i, j, k, l :: 0 <= i < j < |nums| && nums[i] + nums[j] == target &&
                                0 <= k < l < |nums| && nums[k] + nums[l] == target ==>
                                i == k && j == l
  ensures |res| == 2
  ensures 0 <= res[0] < |nums|
  ensures 0 <= res[1] < |nums|
  ensures nums[res[0]] + nums[res[1]] == target
{
  var m: map<int, int> := map[];
  var i := 0;
  while i < |nums|
    // the scope of `i`
    invariant 0 <= i <= |nums|
    // prove that `m` contains all values from `nums[0]` to `nums[i-1]`
    invariant forall j | 0 <= j < i :: nums[j] in m
    // prove that `val == nums[m[val]]`
    invariant forall k | k in m :: 0 <= m[k] < i && k == nums[m[k]]
    // prove that we haven't found the answer yet.
    invariant i > 1 ==> forall j, k | 0 <= j < k < i :: nums[j] + nums[k] != target
    // prove that there will be an answer.
    invariant exists k | i <= k < |nums| ::
                         exists j | 0 <= j < |nums| && k != j ::
                                    nums[k] + nums[j] == target
  {
    var val := target - nums[i];
    if val in m {
      var j := m[val];
      return [j, i];
    }
    m := m[nums[i] := i];
    i := i + 1;
  }
}

method Testing() {
  var nums1 := [2, 7, 11, 15];
  var target1 := 9;
  assert nums1[0] + nums1[1] == target1;
  var res1 := TwoSum(nums1, target1);
  assert nums1[res1[0]] + nums1[res1[1]] == target1;
  print "res1: ", res1, "\n";

  var nums2 := [3,2,4];
  var target2 := 6;
  assert nums2[1] + nums2[2] == target2;
  var res2 := TwoSum(nums2, target2);
  assert nums2[res2[0]] + nums2[res2[1]] == target2;
  print "res2: ", res2, "\n";

  var nums3 := [3,3];
  var target3 := 6;
  assert nums3[0] + nums3[1] == target3;
  var res3 := TwoSum(nums3, target3);
  assert nums3[res3[0]] + nums3[res3[1]] == target3;
  print "res3: ", res3, "\n";
}

method Main() {
  Testing();
}