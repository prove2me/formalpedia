-- Prove2me | solution 1 for mme_CW_q6_fixed_z_difference_code_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T22:16:54.953403+00:00
-- url     : https://prove2.me/submissions/5035f5a5-8125-42cc-a941-940b1ba957a3

import Mathlib
import Definitions.Def_mme_CW_q6_doubled_hash_arithmetic

open MME

set_option autoImplicit false

/-- At modulus greater than two with invertible two, a q=6 address is
determined inside one Z-fiber by its X-minus-Z hash coefficient word. -/
theorem solution
    {M N L G : ℕ} [NeZero M]
    (hM : 2 < M)
    (h2 : IsUnit (2 : ZMod M))
    (e f : CWQ6ExactCoupledAddress N L G)
    (hz : e.1 2 = f.1 2)
    (hcode :
      (fun j =>
        (2 * ((e.1 0 j).val : ZMod M)) -
          (cwQ6CoupledZHashCode (e.1 2 j) : ZMod M)) =
      (fun j =>
        (2 * ((f.1 0 j).val : ZMod M)) -
          (cwQ6CoupledZHashCode (f.1 2 j) : ZMod M))) :
    e = f := by
  have hx : e.1 0 = f.1 0 := by
    funext j
    have hzj : e.1 2 j = f.1 2 j := congrFun hz j
    have hcj := congrFun hcode j
    have hmul :
        (2 : ZMod M) * ((e.1 0 j).val : ZMod M) =
          2 * ((f.1 0 j).val : ZMod M) := by
      rw [hzj] at hcj
      exact sub_left_injective hcj
    have hcast : ((e.1 0 j).val : ZMod M) = ((f.1 0 j).val : ZMod M) :=
      h2.mul_left_cancel hmul
    have hval : (e.1 0 j).val = (f.1 0 j).val := by
      have hval' := congrArg ZMod.val hcast
      simpa only [ZMod.val_natCast_of_lt (by omega : (e.1 0 j).val < M),
        ZMod.val_natCast_of_lt (by omega : (f.1 0 j).val < M)] using hval'
    exact Fin.ext hval
  have hy : e.1 1 = f.1 1 := by
    funext j
    have hxj : e.1 0 j = f.1 0 j := congrFun hx j
    have hzj : e.1 2 j = f.1 2 j := congrFun hz j
    rcases e.2.1 j with he0 | he1 | he2 | he3 <;>
      rcases f.2.1 j with hf0 | hf1 | hf2 | hf3 <;>
      omega
  apply Subtype.ext
  funext i j
  fin_cases i
  · exact congrFun hx j
  · exact congrFun hy j
  · exact congrFun hz j
