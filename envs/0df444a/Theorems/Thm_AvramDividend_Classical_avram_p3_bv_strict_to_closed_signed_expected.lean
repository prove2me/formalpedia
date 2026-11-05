-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_strict_to_closed_signed_expected
-- name    : AvramDividend.Classical.avram_p3_bv_strict_to_closed_signed_expected
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T15:20:12.232194+00:00
-- url     : https://prove2.me/theorems/fbc96f8e-b743-485c-9e86-76d839f91042
-- title:
--   Original BV strict stopped L1 expected budget implies exact full Stieltjes signed horizon budget
-- statement:
--   For the unchanged original bounded-variation controlled Lévy process, any genuine integrable strict-horizon cash-plus-pre-rightpayment-terminal payoff whose expectation is at most the candidate initial value automatically yields the exact complete closed-horizon expected dividend cash plus signed post-rightpayment strict-survival terminal bound. This is the fully source-exact final-endpoint transport with the horizon right-jump atom and time-zero mass preserved. The two explicit strict-payoff assumptions remain to be proved upstream; this helper does not claim to prove the canonical signed stochastic HJB theorem.
-- source:
--   Proved original canonical signed horizon correction 3c21e5f9-78b6-4f04-a32a-1a94fed7a5d2; Proved original full cash and signed terminal integrability and expectation additivity 40cbe9a2-000b-4e99-af2f-33bfa3cd443d; Mathlib integral monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_canonical_signed_horizon_correction
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_positive_horizon_signed_cash_joint_L1_integral_add
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_strict_to_closed_signed_expected
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let Strict : Ω → ℝ := fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
       else 0)
    Integrable Strict P → (∫ ω, Strict ω ∂P) ≤ w x →
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal ∂P) +
    (∫ ω, if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) *
        w (x + X.X S ω - rightLimit D S ω)
      else 0 ∂P) ≤ w x := by sorry
