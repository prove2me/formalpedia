-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB76_original_interior_caplinear_value_exact_minplus_positive_part
-- name    : AvramDividend.Classical.avram_gbB76_original_interior_caplinear_value_exact_minplus_positive_part
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:28:49.427797+00:00
-- url     : https://prove2.me/theorems/7292f9ab-3c36-4693-a606-54efa78cd580
-- title:
--   Original interior finite-cap caplinear payoff equals w(min(y,b)) plus positive part of (y-b)
-- statement:
--   The interior caplinear continuation V_b(y)=w(y) when y≤b and w(b)+(y-b) otherwise is exactly w(min(y,b))+(y-b)^+ for all real reserve values. This representation avoids derivatives at the Gaussian caplinear kink, supplies continuity and uniform continuity on the genuine compact stopped band from continuity of w, and is valid for the actual original value candidate.
-- source:
--   Case split at true interior clipping level b and scalar min/max identities. The clipped function is continuous whenever w is continuous on the appropriate nonnegative reserve interval; no artificial global smoothness is asserted.

import Mathlib
open MeasureTheory Set Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB76_original_interior_caplinear_value_exact_minplus_positive_part
    (w : ℝ → ℝ) (b y : ℝ) :
    (if y ≤ b then w y else w b + (y - b)) =
      w (min y b) + max (y - b) 0 := by sorry
