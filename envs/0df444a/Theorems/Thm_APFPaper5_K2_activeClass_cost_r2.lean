-- Prove2me | Theorems.Thm_APFPaper5_K2_activeClass_cost_r2
-- name    : APFPaper5.K2.activeClass_cost_r2
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-22T15:57:52.282272+00:00
-- url     : https://prove2.me/theorems/69b36b4e-2f3f-4618-8194-4dda7800179e
-- title:
--   activeClass cost
-- statement:
--   Scope and conditions: The successor retains the existing mathematical candidate results while moving three unchanged record-cost lemmas to their own source. The active indicator transforms by permutation without flips and by complementation with flips; the signed candidate transforms with signs. Supplied shared-record examples yield self-overlap four or cancellation to zero. They demonstrate limitations of these candidates and do not adopt a state representation, positive definite physical carrier, or physical hold action. Old native versions and dependents remain unchanged.
--
--   Exact source statement:
--
--   theorem activeClass_cost [Fintype ι] [Fintype W] (w : W → ℝ) (mark : ι → W → Bool)
--       (reads : D → X → Bool) (dist : ι → D) (x : X) :
--       tableForm (atomTable w mark) (activeClass reads dist x) (activeClass reads dist x) =
--         ∑ a, w a * ((∑ i, ind (reads (dist i) x) * ind (mark i a)) *
--           (∑ i, ind (reads (dist i) x) * ind (mark i a)))
--
--   Source parameters:
--
--   universe uI uX uD uW
--   variable {ι : Type uI} {X : Type uX} {D : Type uD} {W : Type uW}
-- source:
--   ['Theorems.Thm_APFPaper5_K2_state_class_candidates:211; USB pullbacks v58 batch B; SHA-256 431ae59f5fdcf92750d333fb33ea70e7067fe8197aab1fa0b80f8447d982d9b6']

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
universe apfNative_uI apfNative_uX apfNative_uD apfNative_uW

theorem APFPaper5.K2.activeClass_cost_r2 :
∀ {ι : Type apfNative_uI} {X : Type apfNative_uX} {D : Type apfNative_uD} {W : Type apfNative_uW}
  [inst : Fintype.{apfNative_uI} ι] [inst_1 : Fintype.{apfNative_uW} W] (w : W → Real) (mark : ι → W → Bool)
  (reads : D → X → Bool) (dist : ι → D) (x : X),
  @Eq.{1} Real
    (@APFPaper5.K1.tableForm.{apfNative_uI} ι inst
      (@APFPaper5.K1.atomTable.{apfNative_uI, apfNative_uW} ι W inst_1 w mark)
      (@APFPaper5.K2.activeClass.{apfNative_uI, apfNative_uX, apfNative_uD} ι X D reads dist x)
      (@APFPaper5.K2.activeClass.{apfNative_uI, apfNative_uX, apfNative_uD} ι X D reads dist x))
    (@Finset.sum.{apfNative_uW, 0} W Real Real.instAddCommMonoid (@Finset.univ.{apfNative_uW} W inst_1) fun (a : W) =>
      @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (w a)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@Finset.sum.{apfNative_uI, 0} ι Real Real.instAddCommMonoid (@Finset.univ.{apfNative_uI} ι inst)
            fun (i : ι) =>
            @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (APFPaper5.K1.ind (reads (dist i) x))
              (APFPaper5.K1.ind (mark i a)))
          (@Finset.sum.{apfNative_uI, 0} ι Real Real.instAddCommMonoid (@Finset.univ.{apfNative_uI} ι inst)
            fun (i : ι) =>
            @HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (APFPaper5.K1.ind (reads (dist i) x))
              (APFPaper5.K1.ind (mark i a))))) := by sorry
