-- Prove2me | solution 1 for polytopeSoftSupport_le_of_forall_directionalValue_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:16:55.284014+00:00
-- url     : https://prove2.me/submissions/0de0575e-f87f-40dd-9cf8-9b8b53d496d9

import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Theorems.Thm_polytopeSoftPartition_pos

set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution
    {u : Finset ℂ} (hu : u.Nonempty) {delta : ℝ} (hdelta : 0 < delta)
    (theta M : ℝ)
    (hM : ∀ z ∈ u, polytopeDirectionalValue z theta ≤ M) :
    polytopeSoftSupport u delta theta ≤
      M + delta * Real.log (u.card : ℝ) := by
  have hsum : polytopeSoftPartition u delta theta ≤
      (u.card : ℝ) * Real.exp (M / delta) := by
    unfold polytopeSoftPartition
    calc
      (∑ z ∈ u, Real.exp (polytopeDirectionalValue z theta / delta)) ≤
          ∑ _z ∈ u, Real.exp (M / delta) := by
        apply Finset.sum_le_sum
        intro z hz
        rw [Real.exp_le_exp]
        exact (div_le_div_iff_of_pos_right hdelta).2 (hM z hz)
      _ = (u.card : ℝ) * Real.exp (M / delta) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : 0 < (u.card : ℝ) := by
    exact_mod_cast hu.card_pos
  have hlog : Real.log (polytopeSoftPartition u delta theta) ≤
      Real.log (u.card : ℝ) + M / delta := by
    have hraw := Real.log_le_log
      (polytopeSoftPartition_pos hu delta theta) hsum
    rw [Real.log_mul hcard.ne' (Real.exp_ne_zero _), Real.log_exp] at hraw
    exact hraw
  unfold polytopeSoftSupport
  calc
    delta * Real.log (polytopeSoftPartition u delta theta) ≤
        delta * (Real.log (u.card : ℝ) + M / delta) :=
      mul_le_mul_of_nonneg_left hlog hdelta.le
    _ = M + delta * Real.log (u.card : ℝ) := by
      field_simp [hdelta.ne']
      ring
