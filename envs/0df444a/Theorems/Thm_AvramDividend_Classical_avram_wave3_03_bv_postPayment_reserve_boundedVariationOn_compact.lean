-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_reserve_boundedVariationOn_compact
-- name    : AvramDividend.Classical.avram_wave3_03_bv_postPayment_reserve_boundedVariationOn_compact
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T18:33:21.649983+00:00
-- url     : https://prove2.me/theorems/73edfc32-dafe-4030-8fa5-9e3f20659099
-- title:
--   Actual post-payment BV Lévy controlled surplus has finite total variation on every compact interval
-- statement:
--   The actual post-payment controlled reserve of a standing bounded-variation spectrally negative Levy process and every adapted nondecreasing genuine dividend path has finite total variation on each compact horizon, simultaneously almost surely, preserving all right-limit dividend jumps including at the origin.
-- source:
--   Uniform finite-grid variation envelope and original BV drift-residual monotonicity, following the exact existing remotely Proved pre-payment reserve eVariationOn argument.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_reserve_partition_variation

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_03_bv_postPayment_reserve_boundedVariationOn_compact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      BoundedVariationOn
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
        (Icc 0 T) := by sorry
