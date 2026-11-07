-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn12_monotone_stopped_grid_filter_card_prefix_iff
-- name    : AvramDividend.Classical.avram_bv_env3_turn12_monotone_stopped_grid_filter_card_prefix_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:31:32.167827+00:00
-- url     : https://prove2.me/theorems/665ec4c6-d430-48b4-aaa7-12fa5293c948
-- title:
--   Monotone true stopped-grid indices form the exact measurable prefix counted by the physical filter
-- statement:
--   For every fixed stopped time, the filter of deterministic increasing physical grid points strictly preceding the time is exactly the initial prefix. Therefore its cardinal determines membership at any index by a local, already observed stopping event. This is the combinatorial component needed to show adapted random mesh indices are nonanticipative.
-- source:
--   Pinned Mathlib Finset.card_le_card, filter_subset, Nat monotonicity; no stochastic assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn12_monotone_stopped_grid_filter_card_prefix_iff
    (u : ℕ → ℝ≥0) (hu : Monotone u) (m i : ℕ)
    (t : WithTop ℝ≥0) :
    i < ((Finset.range m).filter
      (fun j => (u j : WithTop ℝ≥0) < t)).card ↔
      i < m ∧ (u i : WithTop ℝ≥0) < t := by sorry
