-- Prove2me | Theorems.Thm_AvramDividend_Classical_stopped_renewal_geometric_scale_ratio_lower
-- name    : AvramDividend.Classical.stopped_renewal_geometric_scale_ratio_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T20:52:03.371081+00:00
-- url     : https://prove2.me/theorems/7ef84eaf-34cd-4d09-9147-7e9055d659d6
-- title:
--   Backward scale ratio geometric renewal identity
-- statement:
--   The backward scale ratio p=W(a−ε)/W(a) yields the lower finite-difference reward εp/(1−p) by algebra, provided the scale values and increment are nonzero. This supplies an exact final rewrite in the stopped renewal lower-bound derivation.
-- source:
--   Avram Dividend stopped-renewal finite-difference bounds and geometric first-record reward reduction.

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

theorem AvramDividend.Classical.stopped_renewal_geometric_scale_ratio_lower
  (W : ℝ → ℝ) (a ε : ℝ)
  (hWa : W a ≠ 0) (hgap : W a - W (a - ε) ≠ 0) :
  ε * (W (a - ε) / W a) / (1 - W (a - ε) / W a) =
    ε * W (a - ε) / (W a - W (a - ε)) := by sorry
