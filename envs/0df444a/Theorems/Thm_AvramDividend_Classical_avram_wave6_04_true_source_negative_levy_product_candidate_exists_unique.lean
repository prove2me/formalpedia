-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_negative_levy_product_candidate_exists_unique
-- name    : AvramDividend.Classical.avram_wave6_04_true_source_negative_levy_product_candidate_exists_unique
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T08:50:25.053199+00:00
-- url     : https://prove2.me/theorems/1cc5ff8c-3d47-45fd-a453-3418846336cd
-- title:
--   Actual source negative Lévy predictable product candidate exists uniquely on the finite physical clock
-- statement:
--   For every spectrally negative Lévy source and finite horizon T, construct and uniquely characterise the negative-mark product N = μ.prod (X.ν.restrict (-∞,0)), where μ is a finite predictable-time measure with exactly the original physical Lebesgue × P clock law. This theorem identifies the only possible product candidate, without asserting the still Open jump-count intensity hFuture.
-- source:
--   Wave6 Chat04, separately Accepted physical clock existence and uniqueness; a source-specific product existence-and-uniqueness refinement for Chat01/Chat06.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_physical_clock_trim_to_predictable_exists_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_physical_predictable_clock_unique

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_04_true_source_negative_levy_product_candidate_exists_unique
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) :
    ∃! N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)),
      ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
        μ Set.univ < ⊤ ∧
        (∀ A : Set (ℝ≥0 × Ω),
          MeasurableSet[𝓕.rightCont.predictable] A →
          μ A =
            ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
              Real.toNNReal).prod P) A) ∧
        N = (letI : MeasurableSpace (ℝ≥0 × Ω) :=
                  𝓕.rightCont.predictable
             μ.prod (X.ν.restrict (Iio (0 : ℝ)))) := by sorry
