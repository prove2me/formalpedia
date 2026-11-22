-- Prove2me | solution 1 for empiricalError_bounded_diff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:42:24.79545+00:00
-- url     : https://prove2.me/submissions/2dcb84ee-014f-4832-8a7d-53b8085a82bd

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_PAC
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Structures
public import Mathlib.Combinatorics.SetFamily.Shatter
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution {X : Type u}
    (h c : Concept X Bool) (m : ℕ) (hm : 0 < m) :
    HasBoundedDifferences
      (fun xs : Fin m → X =>
        EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool))
      (1 / m : ℝ) := by
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  intro xs j x'
  unfold EmpiricalError
  simp only [Nat.pos_iff_ne_zero.mp hm, ↓reduceIte]
  -- Factor: |sum₁/m - sum₂/m| = |sum₁ - sum₂| / m ≤ 1/m
  rw [← sub_div, abs_div]
  conv_lhs => rw [show |(m : ℝ)| = m from abs_of_nonneg (Nat.cast_nonneg m)]
  -- Goal: |sum₁ - sum₂| / m ≤ 1 / m
  -- Suffices: |sum₁ - sum₂| ≤ 1
  suffices h_bound : |∑ x : Fin m, zeroOneLoss Bool (h (xs x)) (c (xs x)) -
    ∑ x : Fin m, zeroOneLoss Bool (h (Function.update xs j x' x))
      (c (Function.update xs j x' x))| ≤ 1 by
    exact div_le_div_of_nonneg_right h_bound hm_pos.le
  -- The two sums differ only at index j
  rw [← Finset.sum_sub_distrib]
  have key : ∀ i : Fin m, i ≠ j →
    zeroOneLoss Bool (h (xs i)) (c (xs i)) -
    zeroOneLoss Bool (h (Function.update xs j x' i)) (c (Function.update xs j x' i)) = 0 := by
    simp_all
  rw [Finset.sum_eq_single j
    (fun i _ hij => key i hij)
    (fun habs => absurd (Finset.mem_univ j) habs)]
  simp only [Function.update_self]
  -- Now bound |loss₁ - loss₂| ≤ 1
  unfold zeroOneLoss
  split_ifs <;> norm_num
