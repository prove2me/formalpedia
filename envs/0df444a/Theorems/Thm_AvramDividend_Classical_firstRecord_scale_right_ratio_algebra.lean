-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstRecord_scale_right_ratio_algebra
-- name    : AvramDividend.Classical.firstRecord_scale_right_ratio_algebra
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:59:18.3897+00:00
-- url     : https://prove2.me/theorems/a2b419f4-925d-412b-83b7-4886e4ea85dc
-- title:
--   Rewrite immediate geometric first-record reward as right scale quotient
-- statement:
--   The immediate first-record reward with one-step survival ratio p=B/A is exactly the right finite-difference quotient εA/(A−B), provided the scale value and scale increment are nonzero. In the dividend application A=W(a+ε), B=W(a).
-- source:
--   Elementary field algebra applied to the accepted upper geometric first-record renewal bound.

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

theorem AvramDividend.Classical.firstRecord_scale_right_ratio_algebra
    (ε A B : ℝ) (hA : A ≠ 0) (hAB : A - B ≠ 0) :
    ε / (1 - B / A) = ε * A / (A - B) := by sorry
