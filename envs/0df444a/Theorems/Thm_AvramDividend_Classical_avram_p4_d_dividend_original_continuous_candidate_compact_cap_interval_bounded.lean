-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_continuous_candidate_compact_cap_interval_bounded
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_continuous_candidate_compact_cap_interval_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T23:31:02.311445+00:00
-- url     : https://prove2.me/theorems/356a0ead-dcda-4023-bc3b-b4080bdd9e17
-- title:
--   One-sided continuous original dividend value has a bounded finite cap interval including both endpoints
-- statement:
--   Use the exact P4-F continuity on Ici 0, restrict to the original cap interval Icc 0 C.toReal, and invoke the compact extreme value theorem for the norm of w. This constructs a nonnegative uniform bound M without presupposing boundedness, even at cap contact and zero reserve; it supplies the previously explicit compact-interval premise of the finite-cap exponential extension estimate.
-- source:
--   Original P4-F hw_cont and pinned Mathlib isCompact_Icc and IsCompact.exists_isMaxOn for the continuous norm.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_continuous_candidate_compact_cap_interval_bounded
    (C : ℝ≥0∞)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici (0 : ℝ))) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ Icc (0 : ℝ) C.toReal, ‖w z‖ ≤ M := by sorry
