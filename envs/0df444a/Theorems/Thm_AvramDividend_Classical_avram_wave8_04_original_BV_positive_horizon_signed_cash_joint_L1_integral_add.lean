-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_positive_horizon_signed_cash_joint_L1_integral_add
-- name    : AvramDividend.Classical.avram_wave8_04_original_BV_positive_horizon_signed_cash_joint_L1_integral_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:29:38.993958+00:00
-- url     : https://prove2.me/theorems/40cbe9a2-000b-4e99-af2f-33bfa3cd443d
-- title:
--   Original BV positive-time full Stieltjes cash plus signed terminal jointly integrable with exact expectation-additivity
-- statement:
--   Under the source positive-cap BV setup, the complete original discounted Stieltjes cash and strict-survival signed postrightpayment terminal form an integrable real reward, whose expected value is the sum of its two true source expectations. This permits a stopped pathwise Ito-HJB inequality for the combined real reward to imply the exact full cash and terminal budget.
-- source:
--   Avram Proposition 4(i), stopped verification (5.13), original full Stieltjes dividend and signed postrightpayment terminal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_04_original_BV_positive_horizon_signed_cash_joint_L1_integral_add
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    let S : ℝ≥0 := ⟨T,hT⟩
    let Cash : Ω → ℝ := fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    let SignedTerm : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω)
      else 0
    Integrable (fun ω => Cash ω + SignedTerm ω) P ∧
      (∫ ω, Cash ω + SignedTerm ω ∂P) =
        (∫ ω, Cash ω ∂P) + (∫ ω, SignedTerm ω ∂P) := by sorry
