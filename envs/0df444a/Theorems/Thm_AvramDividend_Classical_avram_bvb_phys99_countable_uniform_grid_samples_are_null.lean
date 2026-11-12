-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys99_countable_uniform_grid_samples_are_null
-- name    : AvramDividend.Classical.avram_bvb_phys99_countable_uniform_grid_samples_are_null
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T09:36:13.533199+00:00
-- url     : https://prove2.me/theorems/8335f9d7-f69b-4472-9393-cac371b8af6d
-- title:
--   Countable uniform physical-grid sample points have zero Lebesgue measure
-- statement:
--   The union of every point in a countable sequence of finite uniform physical grids is a measurable null set in Lebesgue measure. This supplies the missing no-grid-contact premise in the phys95 counterexample construction.
-- source:
--   Original BV phys95 contact-set counterexample prerequisite

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.avram_bvb_phys99_countable_uniform_grid_samples_are_null (u : ℕ → ℕ → ℝ) : let G : Set ℝ := Set.range (fun p : ℕ × ℕ => u p.1 p.2); MeasurableSet G ∧ (volume : Measure ℝ) G = 0 := by sorry
