-- Prove2me | Theorems.Thm_AvramDividend_Classical_convex_positive_level_root_unique
-- name    : AvramDividend.Classical.convex_positive_level_root_unique
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T22:51:07.061849+00:00
-- url     : https://prove2.me/theorems/5e34f162-bafc-407a-acc5-0785afe2c4fd
-- title:
--   Uniqueness of a positive level-set root for a convex function vanishing at zero
-- statement:
--   If a real function is convex on the nonnegative half-line, vanishes at zero, and both positive arguments φ₁ and φ₂ attain the same strictly positive value q, then φ₁=φ₂. Convexity makes the secant slope f(t)/t nondecreasing for t>0. If the two positive roots differed, the smaller root would have larger slope q/φ, contradicting monotonicity. The result allows unique identification of the supplied positive Esscher root in the unbounded-variation scale-function argument.
-- source:
--   Pinned Mathlib ConvexOn.slope_mono and slope_def_field. Companion of Proved convex_positive_root_derivative_pos.

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.Ring
open Set

theorem AvramDividend.Classical.convex_positive_level_root_unique
    (f : ℝ → ℝ) (q φ₁ φ₂ : ℝ)
    (hq : 0 < q) (hφ₁ : 0 < φ₁) (hφ₂ : 0 < φ₂)
    (hconv : ConvexOn ℝ (Ici (0 : ℝ)) f)
    (hzero : f 0 = 0)
    (hroot₁ : f φ₁ = q) (hroot₂ : f φ₂ = q) :
    φ₁ = φ₂ := by sorry
