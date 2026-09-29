-- Prove2me | solution 1 for rank_rpow_inv_le_exp_one_of_log_le
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-06-23T21:38:12.359124+00:00
-- url     : https://prove2.me/submissions/3055c8a7-063e-4521-b3dc-105ee36e2d31

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open scoped Real

theorem solution
    (N : ℕ) (q : ℝ) (hN : 1 ≤ N) (hq : 1 ≤ q)
    (hlog : Real.log (N : ℝ) ≤ q) :
    Real.rpow (N : ℝ) q⁻¹ ≤ Real.exp 1 := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le one_pos hNR
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le one_pos hq
  have hlogN_nonneg : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNR
  rw [show Real.rpow (N : ℝ) q⁻¹ = (N : ℝ) ^ (q⁻¹ : ℝ) from rfl,
      Real.rpow_def_of_pos hNpos]
  apply Real.exp_le_exp.mpr
  rw [mul_inv_le_iff₀ hqpos]
  simpa using hlog
