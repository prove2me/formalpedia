-- Prove2me | Theorems.Thm_AvramDividend_Classical_convex_positive_root_derivative_pos
-- name    : AvramDividend.Classical.convex_positive_root_derivative_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:44:35.268071+00:00
-- url     : https://prove2.me/theorems/bd1bf697-af67-477a-9bde-fbed889e02e2
-- title:
--   Derivative is strictly positive at a positive-height root of a convex Laplace-type exponent
-- statement:
--   For a convex function f on [0,∞), if f(0)=0 and f(φ)=q>0 at φ>0, then the chord slope q/φ is positive. Convexity and differentiability at φ imply slope(f,0,φ)≤f'(φ), so f'(φ)>0. Applied to the spectrally negative Lévy Laplace exponent at the positive Esscher root, this yields strictly positive killing/drift coefficient k=ψ'(φ) for the shifted Bernstein descending-ladder-height factorisation.
-- source:
--   Pinned Mathlib ConvexOn.slope_le_deriv and slope_def_field; Lévy exponent convexity.

import Mathlib
open Set

theorem AvramDividend.Classical.convex_positive_root_derivative_pos
    (f : ℝ → ℝ) (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ)
    (hconv : ConvexOn ℝ (Ici (0 : ℝ)) f)
    (hzero : f 0 = 0) (hroot : f φ = q)
    (hderiv : DifferentiableAt ℝ f φ) :
    0 < deriv f φ := by sorry
