-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_strict_signed_witness_native_ennreal_cash
-- name    : AvramDividend.Classical.avram_bv_env3_original_strict_signed_witness_native_ennreal_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T11:51:10.052628+00:00
-- url     : https://prove2.me/theorems/d95ebdbc-4825-4290-a576-cb399475a003
-- title:
--   Original BV strict stopped signed witness implies exact complete Stieltjes cash bound
-- statement:
--   For the original bounded-variation spectrally negative Levy source and a genuine original cap-admissible strategy, an almost-sure strict-horizon physical-source cash plus pre-rightpayment terminal bound by w(x)+M+B with integrable nonpositive-mean signed correction entails the full inclusive Stieltjes dividend cash ENNReal expectation bound. The actual stopped C1 Ito and negative jump compensation needed to construct the signed witness remain explicit external mathematical obligations. The bridge uses the proved original strict L1, strict-to-closed postpayment atom accounting, positive terminal, and real-to-ENNReal conversion.
-- source:
--   Pinned accepted sources 78fa7075, a2794d96, 331f6956 and 67f2cfad; original stopped triple-mesh signed witness 76cf8711 provides the intended antecedent once its source mesh is assembled.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_original_strict_signed_witness_native_ennreal_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0) (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
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
