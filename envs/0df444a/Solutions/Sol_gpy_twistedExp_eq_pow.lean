-- Prove2me | solution 1 for gpy_twistedExp_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T05:07:54.8668+00:00
-- url     : https://prove2.me/submissions/bd307707-30a3-4899-aa90-4d65d984b50f

/- Submission file for `gpy` publish batch `gpy_twistedExp_eq_pow`.
   Self-contained: imports Mathlib only. Top-level `theorem solution`
   is the exact polynomial form of the unconditional twisted absolute
   bound's exponential factor, from GPYDefectSmall.lean
   (`twistedExp_eq_pow`). Unconditional. No defect smallness is claimed:
   this identity is precisely why the unconditional bound is polynomial
   in Q, not polylogarithmic, and cannot by itself show any sum is o(1)
   relative to a polylog-scale main term. -/
import Mathlib

open scoped BigOperators
open scoped Function
open Classical

set_option autoImplicit false


/-- EXACT POLYNOMIAL FORM of the unconditional bound. The
    `exp (2 (k+1)^2 (log Q + 2))` in `abs_twistedMuSqSum_le` is
    literally `exp (4 (k+1)^2) * Q^(2 (k+1)^2)`: polynomial in
    `Q`, not polylogarithmic. -/
theorem solution {k : ℕ} {Q : ℕ} (hQ : 0 < Q) :
    Real.exp (2 * ((k : ℝ) + 1) ^ 2 * (Real.log (Q : ℝ) + 2))
      = Real.exp (4 * ((k : ℝ) + 1) ^ 2) * (Q : ℝ) ^ (2 * (k + 1) ^ 2) := by
  have hN : ((2 * (k + 1) ^ 2 : ℕ) : ℝ) = 2 * ((k : ℝ) + 1) ^ 2 := by
    push_cast
    ring
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQ
  have hexp : Real.exp (2 * ((k : ℝ) + 1) ^ 2 * (Real.log (Q : ℝ) + 2))
      = Real.exp (((2 * (k + 1) ^ 2 : ℕ) : ℝ) * Real.log (Q : ℝ))
        * Real.exp (4 * ((k : ℝ) + 1) ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    rw [hN]
    ring
  rw [hexp, Real.exp_nat_mul, Real.exp_log hQpos]
  exact mul_comm _ _
