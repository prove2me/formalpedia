-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_true_marked_terminal_contact_two_endpoints_count_envelope
-- name    : AvramDividend.Classical.avram_b24_true_marked_terminal_contact_two_endpoints_count_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:27:49.000349+00:00
-- url     : https://prove2.me/theorems/1c6161e9-919c-4d8f-918f-da4ab44bc8cd
-- title:
--   True negative-mark physical terminal contact weighted residual has count-envelope domination
-- statement:
--   For any finite-activity actual original compensated small-negative mark path at two physical last-cell endpoints with intrinsic source values bounded in absolute size by B, and bounded predictable/left-contact coefficients of norm ≤L, the absolute difference between the weighted marked cell source increment and the true surviving negative smallmark terminal atom is bounded by 2LB+L. Each genuine negative smallmark z∈(-1,0) has absolute size below 1, and other large/zero marks contribute zero to this source channel. Combining the original path-uniform integrable B envelope with this deterministic inequality provides a true original stopped mark contact L1 dominator, with no global moment assumptions on large negative marks.
-- source:
--   Scalar triangle inequality, finite smallnegative jump amplitude ≤1, bounded predictable coefficients.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_b24_true_marked_terminal_contact_two_endpoints_count_envelope
    (B L Ja Jb W Wleft z : ℝ)
    (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hJa : ‖Ja‖ ≤ B) (hJb : ‖Jb‖ ≤ B)
    (hW : ‖W‖ ≤ L) (hWleft : ‖Wleft‖ ≤ L) :
    ‖W * (Jb - Ja) -
      Wleft * (if -1 < z ∧ z < 0 then z else 0)‖ ≤
      2 * L * B + L := by sorry
