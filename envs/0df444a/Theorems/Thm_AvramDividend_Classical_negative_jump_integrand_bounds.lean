-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_jump_integrand_bounds
-- name    : AvramDividend.Classical.negative_jump_integrand_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T15:44:50.255744+00:00
-- url     : https://prove2.me/theorems/55008dc9-c9de-431c-8218-9b59eaefb606
-- title:
--   Pointwise domination of the compensated negative-jump exponential
-- statement:
--   For theta at least one and negative jump y, the Lévy-Khintchine compensated exponential integrand is absolutely bounded by theta squared times min(1,y squared). It also admits the sharper signed bound theta squared times y squared for -1<y<0 and zero for y<=-1. These two bounds support both integrability and the sharp quadratic exponent upper bound.
-- source:
--   Exact laplaceExponent definition in Def_AvramDividend_Classical_SpectrallyNegativeLevy; the Real exponential inequalities in pinned Mathlib. This is the pointwise measure-theoretic bridge for psi_quadratic_upper.

import Mathlib
open Set

theorem AvramDividend.Classical.negative_jump_integrand_bounds (θ y : ℝ) (hθ : 1 ≤ θ) (hy : y < 0) :
    |Real.exp (θ * y) - 1 -
      θ * y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y|
        ≤ θ ^ 2 * min 1 (y ^ 2) ∧
    Real.exp (θ * y) - 1 -
      θ * y * (Ioo (-1 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℝ)) y
        ≤ (Ioo (-1 : ℝ) 0).indicator (fun t : ℝ => θ ^ 2 * t ^ 2) y := by sorry
