-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_measurable_countably_selected_raw_path_evaluation
-- name    : AvramDividend.Classical.avram_wave7_01_measurable_countably_selected_raw_path_evaluation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:54:39.031641+00:00
-- url     : https://prove2.me/theorems/a8b2902a-37bf-4d1c-87bd-a5c9677b5954
-- title:
--   Measurable countably selected raw coordinate evaluation on real path space
-- statement:
--   An arbitrary measurable index of a countable grid of nonnegative times can be used to evaluate the raw real path coordinate measurably, even though the index depends on the path. This avoids any incorrect assumption that evaluation at a general real-valued random time is jointly measurable in the raw product σ-algebra. It is a core primitive for dyadic/right-grid sampling around exact intrinsic original Lévy jump-time selectors.
-- source:
--   Express selected evaluation as the single nonzero term of a countable real tsum, use measurable_pi_apply, measurable singletons, Measurable.ite, Measurable.tsum and tsum_ite_eq under pinned Mathlib.

import Mathlib

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_wave7_01_measurable_countably_selected_raw_path_evaluation
    (grid : ℕ → ℝ≥0)
    (index : (ℝ≥0 → ℝ) → ℕ) (hIndex : Measurable index) :
    Measurable (fun Y : ℝ≥0 → ℝ => Y (grid (index Y))) := by sorry
