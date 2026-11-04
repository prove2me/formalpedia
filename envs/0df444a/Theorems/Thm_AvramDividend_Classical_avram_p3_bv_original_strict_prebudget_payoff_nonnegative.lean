-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_prebudget_payoff_nonnegative
-- name    : AvramDividend.Classical.avram_p3_bv_original_strict_prebudget_payoff_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:39:49.156043+00:00
-- url     : https://prove2.me/theorems/bfb4f141-7a0f-4471-b0cd-74afb47c10d1
-- title:
--   Exact original strict-horizon discounted BV cash plus surviving prepayment terminal is pathwise nonnegative
-- statement:
--   For the actual original spectrally negative Levy path, all nonnegative-time stopped discounted Stieltjes cash is nonnegative and the strictly surviving pre-rightpayment terminal is nonnegative at every strictly positive deterministic horizon, directly from the canonical pre-ruin candidate sign condition. This is the source-exact lower envelope for a subsequent Fatou/localisation passage, including time-zero right payments.
-- source:
--   Direct from ENNReal.toReal_nonneg, positivity of real exponential, and the original hw_nonneg at positive times; no stochastic compensation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_strict_prebudget_payoff_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (w : ℝ → ℝ) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (ω : Ω) :
    let S : ℝ≥0 := ⟨T, hT⟩
    0 ≤ (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0) := by sorry
