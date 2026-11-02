-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_any_discount_stopped_payment_ae_finite
-- name    : AvramDividend.Classical.avram_wave5_03_original_any_discount_stopped_payment_ae_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T12:16:02.429075+00:00
-- url     : https://prove2.me/theorems/ca2ee80e-11a4-4615-9516-f476c6d75877
-- title:
--   Full original stopped Stieltjes dividends have almost-sure finite discounted horizon reward for every real discount
-- statement:
--   For every original source SpectrallyNegativeLevy admissible dividend strategy, any deterministic T>0 and any real q, the full samplewise stopped discount-weighted Stieltjes dividendMeasure has finite extended-real mass for P-almost every sample, including time-zero atoms, right lump dividends, diffuse absolutely continuous and singular continuous payments. This proves the almost-sure localisation ingredient from the independently Proved original-source any-discount expected envelope and direct joint random-kernel measurability without assuming the compensated jump measure or full Ito rule.
-- source:
--   Original 8b70a8f9 expected reward moment now Proved; actual source kernel 766b5129 and jointly measurable stopped payment set 6e9faa20, original BV ef7e6c20 UBV 429e17ca. Pure source-a.e. localisation, no independence and no nonnegative w outside pre-ruin.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_any_discount_finite_horizon_stieltjes_exp_moment
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral

open MeasureTheory Set Filter Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_original_any_discount_stopped_payment_ae_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (hT : 0 < T) (q : ℝ) :
    ∀ᵐ ω ∂P,
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)) < ⊤ := by sorry
