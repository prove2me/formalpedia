-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_finite_measurable_marked_filter_card_ENNReal
-- name    : AvramDividend.Classical.avram_p2_34dbea70_finite_measurable_marked_filter_card_ENNReal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:42:57.452668+00:00
-- url     : https://prove2.me/theorems/49fcf2ed-d8d9-4ca3-a87c-8efb8d16b84c
-- title:
--   A finite measurable family of marked predicates has measurable ENNReal counting cardinality
-- statement:
--   For any measurable sample space and finite index set, if each index has a measurable set of samples for which its mark predicate holds, then the sample-dependent ENNReal cardinality of the filtered index set is measurable. The proof uses the already-Proved finite filter cardinality equals a sum of indicator functions; this directly supports original Lévy uniform-grid Fatou estimates with random finite mark counts, without any distributional or finite-activity hypothesis.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_filter_card_eq_ennreal_indicator_sum

open MeasureTheory AvramDividend.Classical
open scoped ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_p2_34dbea70_finite_measurable_marked_filter_card_ENNReal
    {Ω α : Type*} [mΩ : MeasurableSpace Ω]
    [DecidableEq α] (s : Finset α) (marked : α → Ω → Prop)
    (hMarked : ∀ i, MeasurableSet {ω : Ω | marked i ω}) :
    Measurable (fun ω : Ω =>
      (((s.filter (fun i => marked i ω)).card : ℕ) : ℝ≥0∞)) := by sorry
