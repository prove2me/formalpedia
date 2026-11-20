-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_truegrid_zero_clock_payment_sum_is_initial
-- name    : AvramDividend.Classical.avram_pj_workerC_truegrid_zero_clock_payment_sum_is_initial
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T19:33:26.247621+00:00
-- url     : https://prove2.me/theorems/eda7d92b-4705-4377-a024-60c8284ab82f
-- title:
--   At a zero stop the original clipped physical-grid payment correction equals the initial right-jump term
-- statement:
--   For any signed right-payment function, the sum on the original finite ruin-clipped physical grid at stop rho=0 is the single initial value f(0), independently of mesh index. This reveals the nonvanishing zero-clock payment correction in unmasked Ito residuals.
-- source:
--   Direct consequence of Proved 5b1382e2; diagnostic for potentially unsound unmasked source 1f802c9c.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_truegrid_at_zero_clock_is_initial_singleton
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_truegrid_zero_clock_payment_sum_is_initial
    {Ω : Type*} (n k : ℕ) (ρ : Ω → ℝ≥0)
    (ω : Ω) (hzero : ρ ω = 0)
    (f : ℝ≥0 → ℝ) :
    (∑ t ∈ (((Finset.range (k + 1)).image
      (fun i : ℕ => min
        ((i : ℝ≥0) * ((n : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0)))
        (ρ ω))).filter (fun t : ℝ≥0 => t = 0 ∨ t < ρ ω)), f t)
      = f 0 := by sorry
