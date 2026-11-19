-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_purejump_ubv_truncated_negative_rates_diverge
-- name    : AvramDividend.Classical.avram_f6_original_purejump_ubv_truncated_negative_rates_diverge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T17:04:13.520345+00:00
-- url     : https://prove2.me/theorems/5da6ed6a-b810-48fc-a5a5-7f9e2be0f4ab
-- title:
--   Original pure-jump unbounded-variation negative truncated jump rates diverge to infinity
-- statement:
--   For the original spectrally negative Lévy process with no Gaussian coefficient and unbounded variation, its negative-jump truncation rate ν((-∞,-δ)) is finite at every δ>0 and diverges as δ decreases to zero. Uses exact original ν, its Lévy integrability field, existing Proved generic negative-tail rate theorem, and Proved pure-jump UBV infinite negative mass. This source result controls the high-activity marked Poisson truncation scale without postulating stopped Ito budgets.
-- source:
--   Original X.ν, Proved b9b373fa and Proved negative_jump_real_tail_tendsto_top 2cde304a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_purejump_ubv_truncated_negative_rates_diverge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hσ : X.σ = 0) :
    Tendsto (fun δ : ℝ => (X.ν (Iio (-δ))).toReal)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by sorry
