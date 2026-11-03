-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_future_rectangle_compensator_clock_representation_invariant
-- name    : AvramDividend.Classical.avram_wave6_04_true_source_future_rectangle_compensator_clock_representation_invariant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T08:43:54.978587+00:00
-- url     : https://prove2.me/theorems/a0398165-1e8e-4e86-9e00-edfb1f515816
-- title:
--   True source future-rectangle jump compensator transport is independent of physical predictable clock presentation
-- statement:
--   For the original spectrally negative Lévy source and the right-continuous predictable sigma-algebra, if the actual intrinsic jump-count measure has the specified future-rectangle compensation identity against the genuine negative source Lévy measure using one physical predictable clock, then it has exactly the same identity for any other measure agreeing on all physical-time × source-probability predictable sets. This isolates Chat 01's first-moment jump-intensity obligation from the canonical source-clock choice.
-- source:
--   Wave6 Chat04 exact future predictable rectangle representation invariance from the Accepted physical clock uniqueness theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_physical_predictable_clock_unique

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_true_source_future_rectangle_compensator_clock_representation_invariant
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (MT : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (μ₁ μ₂ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ₁ : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
      μ₁ A =
        ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal).prod P) A)
    (hμ₂ : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
      μ₂ A =
        ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal).prod P) A)
    (hFuture₁ : ∀ (i : ℝ≥0) (A : Set Ω) (C : Set ℝ),
      MeasurableSet[𝓕.rightCont i] A → MeasurableSet C →
      MT ((Set.Ioi i ×ˢ A) ×ˢ C) =
        (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
         (μ₁.prod (X.ν.restrict (Iio (0 : ℝ))))
            ((Set.Ioi i ×ˢ A) ×ˢ C))) :
    ∀ (i : ℝ≥0) (A : Set Ω) (C : Set ℝ),
      MeasurableSet[𝓕.rightCont i] A → MeasurableSet C →
      MT ((Set.Ioi i ×ˢ A) ×ˢ C) =
        (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
         (μ₂.prod (X.ν.restrict (Iio (0 : ℝ))))
            ((Set.Ioi i ×ˢ A) ×ˢ C)) := by sorry
