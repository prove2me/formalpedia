-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_aggregate_L1_signed_strict_to_closed_cash
-- name    : AvramDividend.Classical.avram_bv_env3_original_aggregate_L1_signed_strict_to_closed_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T14:15:17.198739+00:00
-- url     : https://prove2.me/theorems/29940c1c-807c-41fe-81d5-895b50b0b401
-- title:
--   Original BV aggregate L1 stopped signed residual yields exact full-horizon ENNReal cash
-- statement:
--   A genuine original stopped strict cash plus prepayment terminal witness bounded by w(x) and one integrable nonpositive-mean signed residual R entails the full closed-horizon expected ENNReal cash bound, preserving the physical horizon atom and without separately splitting martingale and drift integrability. The stochastic original-process inequality remains a required input.
-- source:
--   BV-ENV3 Proved 7fb52983, which transports signed pathwise bounds to full Stieltjes cash; instantiate its martingale slot with R and drift slot with identically zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_original_aggregate_L1_signed_strict_to_closed_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (R : Ω → ℝ) (hRint : Integrable R P)
    (hRmean : (∫ ω, R ω ∂P) ≤ 0)
    (hWitness : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if ENNReal.ofNNReal (⟨T, hT⟩ : ℝ≥0) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D ⟨T, hT⟩ ω)
       else 0) ≤ w x + R ω) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
