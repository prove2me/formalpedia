-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f6_hjb_strict_exit_event_iSup
-- name    : AvramDividend.Classical.avram_p4_f6_hjb_strict_exit_event_iSup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T10:13:13.767993+00:00
-- url     : https://prove2.me/theorems/549fd93e-ce3a-47b3-bb7b-13c826ce3e50
-- title:
--   Strict upper-before-lower exit reward is the supremum of its finite-horizon truncations
-- statement:
--   For any two extended-nonnegative first-passage clocks, the strict upper-first event entails a finite upper clock. Consequently the full upper-first discounted payoff equals the increasing supremum of its payoffs truncated at integer horizons. This pointwise cofinality fact is the source-specific event bridge required before applying the monotone convergence integral budget theorem.
-- source:
--   Source-faithful strict-event truncation lemma for original corrected upper and lower exit times in 8d1164b7-10ee-4fad-92a7-4f012f12ed91. Uses pinned ENNReal.exists_nat_gt to obtain a finite integer cap on any strict-upper-first clock.

import Mathlib
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f6_hjb_strict_exit_event_iSup
    (u d v : ℝ≥0∞) :
    (⨆ n : ℕ, if u < d ∧ u ≤ (n : ℝ≥0∞) then v else 0) =
      (if u < d then v else 0) := by sorry
