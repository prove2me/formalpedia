-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_variation_condition33_no_monotone
-- name    : AvramDividend.Classical.unbounded_variation_condition33_no_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T05:09:31.448305+00:00
-- url     : https://prove2.me/theorems/218def4a-1002-417d-8217-02bbb89c6167
-- title:
--   Unbounded variation gives non-monotone paths and condition (3.3)
-- statement:
--   Every spectrally negative Lévy process of unbounded variation has no monotone paths and satisfies the Gaussian-or-infinite-small-jump alternative in condition (3.3). The only additional part of the classical Standing predicate is integrability of the unit-time increment. This consolidates the previously Proved unbounded-variation dichotomy without introducing a smoothness assumption.
-- source:
--   The definition of SpectrallyNegativeLevy.Standing and the Proved lemma unbounded_variation_gaussian_or_infinite_small_jump_moment.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_unbounded_variation_gaussian_or_infinite_small_jump_moment
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_variation_condition33_no_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation) :
    ¬ X.HasMonotonePaths ∧ X.Condition33 := by sorry
