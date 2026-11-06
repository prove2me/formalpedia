-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_strict_residual_to_expected_prebudget
-- name    : AvramDividend.Classical.avram_p3_2_original_strict_residual_to_expected_prebudget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T14:18:33.082575+00:00
-- url     : https://prove2.me/theorems/1b5a4ba0-942e-4112-92fe-b774b423d361
-- title:
--   Genuine integrable original strict residual implies actual stopped real expectation budget
-- statement:
--   For the actual original X.X/D admissible strategy, any integrable nonpositive-mean residual bounding strict Iio T cash and the strictly surviving pre-rightpayment terminal implies the exact real expected prebudget. It uses Proved original L1 integrability and does not import the canonical residual.
-- source:
--   Full non-circular expectation integration from Proved original prebudget L1 theorem 78fa7075-2712-494f-a233-a4de325f68fd, integral_mono_ae and probability-one constant integral. The original physical residual is an explicit hypothesis rather than any Open canonical import.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_prebudget_L1

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_strict_residual_to_expected_prebudget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (E : Ω → ℝ) (hEInt : Integrable E P)
    (hEMean : (∫ ω, E ω ∂P) ≤ 0)
    (hStrict : ∀ᵐ ω ∂P,
      let S : ℝ≥0 := ⟨T, hT⟩
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0) ≤ w x + E ω) :
    let S : ℝ≥0 := ⟨T, hT⟩
    (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0) ∂P) ≤ w x := by sorry
