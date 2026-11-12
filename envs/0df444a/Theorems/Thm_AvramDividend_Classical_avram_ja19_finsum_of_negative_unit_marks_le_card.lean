-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja19_finsum_of_negative_unit_marks_le_card
-- name    : AvramDividend.Classical.avram_ja19_finsum_of_negative_unit_marks_le_card
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:17:24.33999+00:00
-- url     : https://prove2.me/theorems/267480d6-7b34-48a8-91b8-59bf69f00539
-- title:
--   Absolute finite sum of negative unit-bounded marks at most cardinality
-- statement:
--   For any finite index set and real-valued marks bounded between -1 and 0, the absolute sum of those marks is at most the cardinality of the index set. This is a reusable finite algebra step for the original same-space Poisson jump-count comparison.
-- source:
--   J-A19 bounded marked sum algebra

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja19_finsum_of_negative_unit_marks_le_card
    {α : Type*} [DecidableEq α] (F : Finset α) (g : α → ℝ)
    (hlo : ∀ u ∈ F, -1 ≤ g u)
    (hhi : ∀ u ∈ F, g u ≤ 0) :
    |∑ u ∈ F, g u| ≤ (F.card : ℝ) := by sorry
