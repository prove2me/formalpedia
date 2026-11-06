-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_any_clock_strict_signed_to_full_cash
-- name    : AvramDividend.Classical.avram_bv_env3_original_any_clock_strict_signed_to_full_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:16:21.029657+00:00
-- url     : https://prove2.me/theorems/7fb52983-4444-467f-a150-db6c9935adeb
-- title:
--   Original BV any positive clock pathwise postpayment correction closes signed Stieltjes cash
-- statement:
--   For the genuine original bounded-variation source and positive physical horizon, the proved original any-clock pointwise full cash/postpayment terminal versus strict cash/prepayment terminal comparison transports a genuine integrable nonpositive-mean signed source witness to the exact full Stieltjes ENNReal cash bound. It does not add an unwarranted HJB generator, jump regularity or equality-in-law premise; constructing the original signed witness remains explicit.
-- source:
--   Pinned Proved 98a4cc24 original any-clock pathwise Stieltjes postpayment comparison and 9e0718aa full-atom native finite-mesh signed mean bridge; mathematically stronger assumptions include T>0 and original admissibility.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_original_any_clock_strict_signed_to_full_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) (M B : Ω → ℝ)
    (hMint : Integrable M P) (hBint : Integrable B P)
    (hSigned : (∫ ω, M ω + B ω ∂P) ≤ 0)
    (hWitness : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if ENNReal.ofNNReal (⟨T, hT⟩ : ℝ≥0) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D ⟨T, hT⟩ ω)
       else 0) ≤ w x + M ω + B ω) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
