-- Prove2me | Theorems.Thm_APFPaper5_K2_sideClass_after_hold_r2
-- name    : APFPaper5.K2.sideClass_after_hold_r2
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-22T16:03:50.2912+00:00
-- url     : https://prove2.me/theorems/d2cfdeed-e4d1-44db-9685-0ce23b879c38
-- title:
--   sideClass after hold
-- statement:
--   Scope and conditions: The successor retains the existing mathematical candidate results while moving three unchanged record-cost lemmas to their own source. The active indicator transforms by permutation without flips and by complementation with flips; the signed candidate transforms with signs. Supplied shared-record examples yield self-overlap four or cancellation to zero. They demonstrate limitations of these candidates and do not adopt a state representation, positive definite physical carrier, or physical hold action. Old native versions and dependents remain unchanged.
--
--   Exact source statement:
--
--   theorem sideClass_after_hold (reads : D → X → Bool) (dist : ι → D) (h : X → X)
--       (sigma : ι → ι) (flip : ι → Bool) (r : RearrangesFamily reads dist h sigma flip)
--       (i : ι) (x : X) :
--       sideClass reads dist (h x) i =
--         (if flip i then (-1 : ℝ) else 1) * heldAfter sigma (sideClass reads dist x) i
--
--   Source parameters:
--
--   universe uI uX uD uW
--   variable {ι : Type uI} {X : Type uX} {D : Type uD} {W : Type uW}
-- source:
--   ['Theorems.Thm_APFPaper5_K2_state_class_candidates:230; USB pullbacks v58 batch B; SHA-256 431ae59f5fdcf92750d333fb33ea70e7067fe8197aab1fa0b80f8447d982d9b6']

import Definitions.Def_APFPaper5_K2_StateClass_r2
import Definitions.Def_APFPaper5_K2_HoldScore
import Theorems.Thm_APFPaper5_K2_ind_mul_self
import Theorems.Thm_APFPaper5_K2_keptClass_cost_r2
import Theorems.Thm_APFPaper5_K2_keptClass_union_of_disjoint_r2
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
set_option autoImplicit false
universe apfNative_uI apfNative_uX apfNative_uD

theorem APFPaper5.K2.sideClass_after_hold_r2 :
∀ {ι : Type apfNative_uI} {X : Type apfNative_uX} {D : Type apfNative_uD} (reads : D → X → Bool) (dist : ι → D)
  (h : X → X) (sigma : ι → ι) (flip : ι → Bool)
  (r : @APFPaper5.K2.RearrangesFamily.{apfNative_uI, apfNative_uX, apfNative_uD} ι X D reads dist h sigma flip) (i : ι)
  (x : X),
  @Eq.{1} Real (@APFPaper5.K2.sideClass.{apfNative_uI, apfNative_uX, apfNative_uD} ι X D reads dist (h x) i)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@ite.{1} Real (@Eq.{1} Bool (flip i) Bool.true) (instDecidableEqBool (flip i) Bool.true)
        (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      (@APFPaper5.K2.heldAfter.{apfNative_uI} ι sigma
        (@APFPaper5.K2.sideClass.{apfNative_uI, apfNative_uX, apfNative_uD} ι X D reads dist x) i)) := by sorry
