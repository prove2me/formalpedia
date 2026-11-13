-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva82_original_zero_horizon_compensator_clock_and_real_integrals
-- name    : AvramDividend.Classical.avram_bva82_original_zero_horizon_compensator_clock_and_real_integrals
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T21:25:38.420101+00:00
-- url     : https://prove2.me/theorems/5ad15169-b86d-4fea-99e2-0fd58368a64e
-- title:
--   Original zero-horizon mapped Lebesgue compensator clock and real integrals vanish
-- statement:
--   When the exact original negative-mark compensator's clock uses real Lebesgue measure restricted to Icc 0 0 then mapped into nonnegative time, it vanishes, hence every kernel's integral is zero. This closes the deterministic compensator half of original M(0).

import Mathlib
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva82_original_zero_horizon_compensator_clock_and_real_integrals :
    let μ : Measure ℝ≥0 :=
      (((volume : Measure ℝ).restrict (Icc (0 : ℝ) 0)).map Real.toNNReal)
    μ = 0 ∧ ∀ f : ℝ≥0 → ℝ, (∫ t, f t ∂μ) = 0 := by sorry
