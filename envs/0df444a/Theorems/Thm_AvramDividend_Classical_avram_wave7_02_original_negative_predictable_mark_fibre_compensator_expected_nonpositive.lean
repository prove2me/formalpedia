-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_negative_predictable_mark_fibre_compensator_expected_nonpositive
-- name    : AvramDividend.Classical.avram_wave7_02_original_negative_predictable_mark_fibre_compensator_expected_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:03:28.980323+00:00
-- url     : https://prove2.me/theorems/bc2cc4b6-16ee-4ae1-9f72-c37e7035b055
-- title:
--   Original negative predictable signed mark physical time compensator is L1 and has nonpositive expected value
-- statement:
--   For the original spectrally negative Levy X on its right-continuous filtration, a predictable-measurable, integrable and pointwise nonpositive signed negative-mark kernel has a genuine finite physical-time compensator with pathwise L1 integrability and nonpositive expectation. This uses the proved original signed predictable fibre Fubini lemma, retaining the exact original filtration and Levy measure and requiring no first small-jump moment. The identification of realised source jumps with their compensation remains a separate obligation.
-- source:
--   Proved original right-continuous predictable physical-clock Fubini 6fdb8989. Use integrable signed product integral nonpositivity for a genuinely original ν-negative-mark kernel.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_original_rightcont_predictable_signed_mark_compensator_fibre_Fubini
open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_negative_predictable_mark_fibre_compensator_expected_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hGMeas : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable)
      (inferInstance : MeasurableSpace ℝ))] G)
    (hGNeg : ∀ p, G p ≤ 0)
    (hGInt : ∀ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ →
      (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
        Integrable G (μ.prod (X.ν.restrict (Iio (0 : ℝ)))))) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
        μ A = ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal).prod P) A) ∧
      Integrable (fun ω => ∫ t, ∫ z, G ((t, ω), z)
        ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal)) P ∧
      (∫ ω, (∫ t, ∫ z, G ((t, ω), z)
        ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal)) ∂P) ≤ 0 := by sorry
