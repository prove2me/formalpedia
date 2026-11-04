-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_34dbea70_marked_rectangle_disjoint_mark_add
-- name    : AvramDividend.Classical.avram_p2_34dbea70_marked_rectangle_disjoint_mark_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:46:30.492542+00:00
-- url     : https://prove2.me/theorems/46f8ce7c-df57-4108-9fa4-c0dad477e47b
-- title:
--   Disjoint Borel jump mark rectangles have additive source measure
-- statement:
--   For an arbitrary measure on the original nonnegative-time and real-mark product space, its value on a time rectangle marked by a disjoint Borel union is the sum of the values of the two marked rectangles. This deterministic lemma applies directly to the literal intrinsic original jump-count measure, without assuming a Lévy-rate identity.

import Mathlib

open MeasureTheory Set
open scoped ENNReal NNReal

theorem AvramDividend.Classical.avram_p2_34dbea70_marked_rectangle_disjoint_mark_add (μ : Measure (ℝ≥0 × ℝ)) (T : ℝ≥0) (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C) (hBC : Disjoint B C) : μ (Ioc 0 T ×ˢ (B ∪ C)) = μ (Ioc 0 T ×ˢ B) + μ (Ioc 0 T ×ˢ C) := by sorry
