-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_midpoint_multiplicative_of_ratio_order
-- name    : AvramDividend.Classical.positive_midpoint_multiplicative_of_ratio_order
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T09:23:01.430302+00:00
-- url     : https://prove2.me/theorems/94c1f8ec-43eb-4fa7-a9cf-641fdc507c66
-- title:
--   Ratio comparison implies multiplicative midpoint concavity for positive functions
-- statement:
--   For any strictly positive function on the positive axis, the ordering f(x)/f(x+t)≤f(y)/f(y+t) for x≤y and t>0 implies f(x)f(y)≤f((x+y)/2)^2. Apply the ratio comparison at x and the midpoint with equal increments, then clear positive denominators. This is the deterministic midpoint component of the log-concavity route: corrected shifted-exit comparison plus an independently proved exit-scale identity supplies the ratio ordering for the canonical scale function.
-- source:
--   Elementary multiplicative midpoint log-concavity criterion, applied to two-sided exit scale-function ratios in Kuznetsov, Kyprianou and Rivero (2013).

import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical

theorem AvramDividend.Classical.positive_midpoint_multiplicative_of_ratio_order
    (f : ℝ → ℝ)
    (hfpos : ∀ x : ℝ, 0 < x → 0 < f x)
    (hratio : ∀ x y t : ℝ, 0 < x → x ≤ y → 0 < t →
      f x / f (x + t) ≤ f y / f (y + t)) :
    ∀ x y : ℝ, 0 < x → x < y →
      f x * f y ≤ (f ((x + y) / 2)) ^ 2 := by sorry
