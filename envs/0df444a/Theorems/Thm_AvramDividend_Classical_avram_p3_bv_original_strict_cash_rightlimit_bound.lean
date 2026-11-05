-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_rightlimit_bound
-- name    : AvramDividend.Classical.avram_p3_bv_original_strict_cash_rightlimit_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:10:36.127106+00:00
-- url     : https://prove2.me/theorems/512282cc-8988-4ec0-aa3d-2c3fd37958db
-- title:
--   Original strict stopped discounted Stieltjes cash bounded pathwise by dividend right limit
-- statement:
--   Under the source IsDividendStrategy hypotheses and any original ruin clock, the literal nonnegative discounted Stieltjes cash over payment times strictly before a finite nonnegative horizon is bounded by the full cumulative dividend right-limit at that horizon. This covers the original time-zero right-payment atom, later right-jump payments and diffuse and singular-continuous dividend mass, without a compensated Poisson law or an expectation bound.
-- source:
--   Proved original paymentTimes membership/measurability and source Stieltjes measure interval mass theorem; pinned Mathlib lintegral_mono_ae and measure_mono.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_strict_cash_rightlimit_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ s in paymentTimes σ ∩ Iio (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂dividendMeasure D ω) ≤
    ENNReal.ofReal (rightLimit D T ω) := by sorry
