-- Prove2me | Theorems.Thm_AvramDividend_Classical_convex_positive_root_secant_lower
-- name    : AvramDividend.Classical.convex_positive_root_secant_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T22:54:09.158207+00:00
-- url     : https://prove2.me/theorems/1e8e06f5-7a50-4a00-9a98-ef94013e5224
-- title:
--   Linear lower increment at a positive root of a convex exponent
-- statement:
--   For a convex real function f on [0,∞) with f(0)=0, f(φ)=q>0 at a positive root φ, the forward increment is bounded below by the origin-to-root chord slope: f(φ+θ)-q ≥ (q/φ)θ for θ>0. This scalar inequality provides the linear resolvent denominator needed in the Esscher-tilted scale-function uniform-bound argument: it gives ψ(φ+θ)-q ≥ (q/φ)θ without invoking a differentiability or renewal theorem.
-- source:
--   Pinned Mathlib ConvexOn.slope_mono and slope_def_field, combined with positive-denominator inequalities.

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
open Set

theorem AvramDividend.Classical.convex_positive_root_secant_lower
    (f : ℝ → ℝ) (q φ θ : ℝ)
    (hq : 0 < q) (hφ : 0 < φ) (hθ : 0 < θ)
    (hconv : ConvexOn ℝ (Ici (0 : ℝ)) f)
    (hzero : f 0 = 0) (hroot : f φ = q) :
    (q / φ) * θ ≤ f (φ + θ) - q := by sorry
