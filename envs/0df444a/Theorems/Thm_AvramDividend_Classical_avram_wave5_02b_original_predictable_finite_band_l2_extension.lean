-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02b_original_predictable_finite_band_l2_extension
-- name    : AvramDividend.Classical.avram_wave5_02b_original_predictable_finite_band_l2_extension
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:57:35.112185+00:00
-- url     : https://prove2.me/theorems/790226fb-034e-4ed6-a179-50d03ffed03c
-- title:
--   Original-source predictable finite-band isometry extends to all L² kernels
-- statement:
--   For the actual original Lévy process and intrinsic jump measure, suppose a centred linear map on the span of original predictable marked rectangles has the elementary L² isometry and agrees almost surely with the pathwise compensated source integral. For a finite predictable marked energy measure, the original-filtration rectangle density yields a continuous linear isometry on all L² kernels, centred on the original probability space and retaining the actual-source representation on its elementary domain. The elementary linear isometry, its centring and source representation are explicit hypotheses; identification of the energy measure with physical Lévy intensity and extension of the source representation beyond elementary kernels remain separate obligations.
-- source:
--   Proved original predictable marked finite-band L² density a44fb480-7fcb-4bde-9fe7-8b82c4ac97e3, dense isometry extension 8ddd4ece-4ffe-4b62-a14c-bea4eeabfc1c and original-probability L² expectation continuity d2c2ff3c-9bb4-44f4-a158-a327ccc7a8a7.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_original_filtration_marked_finite_band_l2_dense
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_dense_elementary_l2_isometry_extension
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_probability_l2_expectation_continuous_original_space

open MeasureTheory MeasurableSpace Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_02b_original_predictable_finite_band_l2_extension
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    [mAll : MeasurableSpace ((ℝ≥0 × Ω) × ℝ)]
    (μ : Measure ((ℝ≥0 × Ω) × ℝ)) [IsFiniteMeasure μ]
    (hAll : mAll = (𝓕.predictable).prod
      (inferInstance : MeasurableSpace ℝ))
    (R : Set (Lp ℝ (2 : ℝ≥0∞) μ))
    (hR : R =
      {v | ∃ (t : Set ((ℝ≥0 × Ω) × ℝ)),
        t ∈ insert Set.univ (insert (∅ : Set ((ℝ≥0 × Ω) × ℝ))
          (Set.image2 (· ×ˢ ·)
            {S | (∃ A : Set Ω, MeasurableSet[𝓕 ⊥] A ∧
                        S = ({⊥} ×ˢ A)) ∨
                 (∃ i : ℝ≥0, ∃ A : Set Ω, MeasurableSet[𝓕 i] A ∧
                        S = (Set.Ioi i ×ˢ A))}
            {C : Set ℝ | MeasurableSet C})) ∧
        ∃ (htm : MeasurableSet t) (hμt : μ t ≠ ⊤),
          indicatorConstLp (2 : ℝ≥0∞) htm hμt (1 : ℝ) = v})
    (S : Submodule ℝ (Lp ℝ (2 : ℝ≥0∞) μ))
    (hS : S = Submodule.span ℝ R)
    (I₀ : S →ₗ[ℝ] Lp ℝ (2 : ℝ≥0∞) P)
    (hIsom : ∀ x : S, ‖I₀ x‖ = ‖(x : Lp ℝ (2 : ℝ≥0∞) μ)‖)
    (hZero : ∀ x : S, ∫ ω, I₀ x ω ∂P = 0)
    (clock : Measure ℝ≥0) (ν : Measure ℝ)
    (hSource : ∀ x : S, (I₀ x : Ω → ℝ) =ᵐ[P] fun ω =>
      (∫ p, ((x : Lp ℝ (2 : ℝ≥0∞) μ) : ((ℝ≥0 × Ω) × ℝ) → ℝ)
        ((p.1, ω), p.2) ∂(NX ω)) -
      ∫ t, ∫ z, ((x : Lp ℝ (2 : ℝ≥0∞) μ) :
        ((ℝ≥0 × Ω) × ℝ) → ℝ) ((t, ω), z) ∂ν ∂clock) :
    ∃ I : Lp ℝ (2 : ℝ≥0∞) μ →L[ℝ] Lp ℝ (2 : ℝ≥0∞) P,
      (∀ x : S, I (x : Lp ℝ (2 : ℝ≥0∞) μ) = I₀ x) ∧
      (∀ v, ‖I v‖ = ‖v‖) ∧
      (∀ v, ∫ ω, I v ω ∂P = 0) ∧
      (∀ x : S, (I (x : Lp ℝ (2 : ℝ≥0∞) μ) : Ω → ℝ) =ᵐ[P]
        fun ω =>
          (∫ p, ((x : Lp ℝ (2 : ℝ≥0∞) μ) : ((ℝ≥0 × Ω) × ℝ) → ℝ)
            ((p.1, ω), p.2) ∂(NX ω)) -
          ∫ t, ∫ z, ((x : Lp ℝ (2 : ℝ≥0∞) μ) :
            ((ℝ≥0 × Ω) × ℝ) → ℝ) ((t, ω), z) ∂ν ∂clock) := by sorry
