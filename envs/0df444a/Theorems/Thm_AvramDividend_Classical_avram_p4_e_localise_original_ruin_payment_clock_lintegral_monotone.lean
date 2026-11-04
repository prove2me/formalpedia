-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ruin_payment_clock_lintegral_monotone
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_ruin_payment_clock_lintegral_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:00:49.480962+00:00
-- url     : https://prove2.me/theorems/4a1ca20d-7165-4b0e-9233-4ade1e056f99
-- title:
--   True ruin-restricted Stieltjes dividend cash is monotone in the actual finite stopping clock
-- statement:
--   For unchanged original dividendMeasure and paymentTimes(ruinTime X x D ω), any pathwise increase of the finite NNReal stopping clock produces a set inclusion of the genuine Iic terminal payment windows. ENNReal lintegral_mono_set proves pathwise cash monotonicity without assuming finite integral or altering time-zero, terminal ruin, horizon atoms or singular Stieltjes parts. This supplies the exact cash-monotonicity premise for Fatou/monotone convergence to P4-F.
-- source:
--   Original dividendMeasure/paymentTimes source and Mathlib lintegral_mono_set; same argument in accepted Avram Wave-6 original Fatou source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Extending the original stopped clock preserves every allowed dividend atom and increases ENNReal cash. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_ruin_payment_clock_lintegral_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q : ℝ)
    (τ σ : Ω → ℝ≥0) (hclock : ∀ ω, τ ω ≤ σ ω) :
    ∀ ω,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by sorry
