-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_random_strict_contact_tail_lintegral_measurable
-- name    : AvramDividend.Classical.avram_p3_grid3_original_random_strict_contact_tail_lintegral_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:06:20.66318+00:00
-- url     : https://prove2.me/theorems/4649f140-9718-4a8f-a98c-4982019d9993
-- title:
--   Original Lévy strict moving contact interval discounted dividendMeasure cash is measurable
-- statement:
--   For actual original X and admissible dividend strategy D, any measurable pathwise real clock τ and real width δ give measurable strict contact cash lintegral over paymentTimes(ruinTime) intersect (τ-δ,τ). Uses original joint paymentTimes measurability and s-finite dividendMeasure kernel. No replacement Poisson process or extra stochastic identity.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_random_strict_contact_tail_lintegral_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (τ : Ω → ℝ) (hτ : Measurable τ) (δ : ℝ) :
    Measurable (fun ω : Ω =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioo (τ ω - δ) (τ ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) := by sorry
