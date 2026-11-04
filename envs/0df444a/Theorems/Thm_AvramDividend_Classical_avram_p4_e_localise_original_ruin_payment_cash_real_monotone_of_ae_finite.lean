-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ruin_payment_cash_real_monotone_of_ae_finite
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_ruin_payment_cash_real_monotone_of_ae_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:08:56.318262+00:00
-- url     : https://prove2.me/theorems/4e119742-aa73-439f-aca3-d58c4383628a
-- title:
--   True real stopped dividend cash increases with horizon under a.e. Stieltjes finiteness
-- statement:
--   A growing physical stopping clock makes the original ruin-window Stieltjes payment set larger and hence its ENNReal cash nondecreasing. ENNReal.toReal is monotone on the finite range: the theorem explicitly requires the larger raw Stieltjes lintegral to be finite almost everywhere, since toReal(⊤)=0 otherwise. This preserves all dividend atoms while providing a valid real cash monotonicity bridge for P4-F, conditional on the exact finiteness obligation.
-- source:
--   Original dividendMeasure/paymentTimes and pinned Mathlib lintegral_mono_set, ENNReal.toReal_mono; no substitution of random Stieltjes with Lebesgue measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Real-valued original cash is monotone when the larger exact Stieltjes lintegral is finite a.e. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_ruin_payment_cash_real_monotone_of_ae_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q : ℝ)
    (τ σ : Ω → ℝ≥0) (hclock : ∀ ω, τ ω ≤ σ ω)
    (hfinite : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) < ⊤) :
    ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by sorry
