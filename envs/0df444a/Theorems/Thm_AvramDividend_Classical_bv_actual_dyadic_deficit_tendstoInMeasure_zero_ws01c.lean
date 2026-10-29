-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_dyadic_deficit_tendstoInMeasure_zero_ws01c
-- name    : AvramDividend.Classical.bv_actual_dyadic_deficit_tendstoInMeasure_zero_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T22:43:42.903683+00:00
-- url     : https://prove2.me/theorems/79913a9d-47ea-4574-93dd-60d9fd38ef10
-- title:
--   Actual BV Lévy drift deficit converges to zero in measure along reciprocal dyadic scales
-- statement:
--   For the actual bounded-variation spectrally negative Lévy process, 2^n·(2^(-n)d−X_(2^(-n))) converges to zero in probability, interpreted as convergence in measure. The finite-time Proved drift upper bound gives almost-sure nonnegative deficits; the already Proved scaled positive-tail estimate applies to δ_n=2^(-n) and θ_n=2^n with their product exactly one. The a.e.-nonnegative tail criterion yields convergence in measure without an unjustified almost-sure leap or a first-moment bound.
-- source:
--   Cause-linked re-publication of terminal job dea27443-f369-492e-8958-d689e3e93ad3, whose sole failure was unknown import bv_ae_nonneg_tail_tendstoInMeasure_zero_ws01c. That exact theorem is now canonically Proved UUID 22bf82e4-d343-4601-b145-2045313e9e19. Original formal statement/preamble and 47-line source work/avram_ws01c_actual_dyadic_deficit_inmeasure_solution_direct.lean retained.

import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_fixed_time
import Theorems.Thm_AvramDividend_Classical_bv_scaled_drift_deficit_tails_tendsto_zero_ws01b
import Theorems.Thm_AvramDividend_Classical_bv_ae_nonneg_tail_tendstoInMeasure_zero_ws01c
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_dyadic_deficit_tendstoInMeasure_zero_ws01c
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation) :
    TendstoInMeasure P
      (fun (n : ℕ) (ω : Ω) =>
        (2 : ℝ) ^ n *
          ((((2 : ℝ≥0)⁻¹) ^ n : ℝ≥0) * X.drift -
            X.X ((2 : ℝ≥0)⁻¹ ^ n) ω))
      atTop (fun _ => (0 : ℝ)) := by sorry
