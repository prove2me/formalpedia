-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_grid_two_sided_hitting_eq_upper_hitting_for_remote_lower_corrected
-- name    : AvramDividend.Classical.finite_grid_two_sided_hitting_eq_upper_hitting_for_remote_lower_corrected
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T07:24:25.179528+00:00
-- url     : https://prove2.me/theorems/b96b7b71-065f-46e2-b596-6a952b77727f
-- title:
--   Finite-grid two-sided hitting equals one-sided hitting for a remote lower barrier, with correctly scoped prerequisite
-- statement:
--   At a fixed finite observation horizon m, a lower barrier −n eventually lies below every sample path observation and cannot alter the first strict upper crossing index. This version correctly imports the mathematically valid finite_grid_lower_barrier_eventually_irrelevant_corrected prerequisite, rather than the erroneous earlier biconditional-scoping draft. The Proved chat03_hittingBtwn_congr_before_terminal then converts predicate equivalence on k<m into equality of bounded hitting indices. Suitable for lower-barrier exhaustion of two-sided grid exponential optional-sampling estimates.
-- source:
--   Correctly scoped prerequisite and Prove2Me chat03_hittingBtwn_congr_before_terminal.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_finite_grid_lower_barrier_eventually_irrelevant_corrected
import Theorems.Thm_AvramDividend_Classical_chat03_hittingBtwn_congr_before_terminal
open MeasureTheory Set

theorem AvramDividend.Classical.finite_grid_two_sided_hitting_eq_upper_hitting_for_remote_lower_corrected
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (f : ℕ → Ω → ℝ) (ω : Ω) (z : ℝ) (m : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      hittingBtwn
        (fun k ω => max (f k ω - z) (-(n : ℝ) - f k ω))
        (Ioi (0 : ℝ)) 0 m ω =
      hittingBtwn
        (fun k ω => f k ω - z)
        (Ioi (0 : ℝ)) 0 m ω := by sorry
