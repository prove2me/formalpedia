-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_02_original_rightcont_predictable_signed_mark_compensator_fibre_Fubini
-- name    : AvramDividend.Classical.avram_wave6_02_original_rightcont_predictable_signed_mark_compensator_fibre_Fubini
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T09:30:12.651546+00:00
-- url     : https://prove2.me/theorems/6fdb8989-a9bf-46e9-943b-4e9b9e07f0f6
-- title:
--   Actual original signed right-continuous predictable Lévy mark compensator has integrable pathwise physical-time fibres and exact P expectation
-- statement:
--   For any signed real marked G predictable with respect to the original Lévy X right-continuous filtration and integrable against the genuine μ×X.ν negative-mark intensity, construct its actual finite physical predictable clock μ and prove the pathwise sample compensator ∫ time∫ negative Lévy marks G((t,ω),z) is P-integrable, with original P expectation equal to the full signed original μ×X.ν compensator. Unlike deterministic centring, this controls the actual random finite-variation compensator term needed for stopped Itô–Meyer; no first small-jump moment. Uses exact predictability and is independent of the still Open Chat01 source-rectangle law.
-- source:
--   Canonical original predictable trim physical clock 16857b34. Establish μ=ξ.trim via exact measurable-set equality. Use source-negative SFinite, Integrable.integral_prod_left, strongly measurable mark sections, integrable_of_integrable_trim, integral_trim, integral_prod_symm, Integrable.integral_prod_right.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_source_finite_horizon_predictable_lintegral_eq_time_probability
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_02_original_rightcont_predictable_signed_mark_compensator_fibre_Fubini
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
        μ A = ((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      (∀ G : ((ℝ≥0 × Ω) × ℝ) → ℝ,
        Measurable[(@Prod.instMeasurableSpace _ _
          (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ))] G →
        (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
          Integrable G (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) →
        Integrable
          (fun ω => ∫ t, ∫ z, G ((t, ω), z)
            ∂(X.ν.restrict (Iio (0 : ℝ)))
            ∂(((volume : Measure ℝ).restrict
              (Icc 0 (T : ℝ))).map Real.toNNReal)) P ∧
        (∫ ω, (∫ t, ∫ z, G ((t, ω), z)
          ∂(X.ν.restrict (Iio (0 : ℝ)))
          ∂(((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal)) ∂P) =
        (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
          ∫ p, G p ∂(μ.prod (X.ν.restrict (Iio (0 : ℝ)))))) := by sorry
