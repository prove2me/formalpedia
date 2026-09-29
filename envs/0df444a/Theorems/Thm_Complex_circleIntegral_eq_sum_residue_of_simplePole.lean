-- Prove2me | Theorems.Thm_Complex_circleIntegral_eq_sum_residue_of_simplePole
-- name    : Complex.circleIntegral_eq_sum_residue_of_simplePole
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/6246bb8f-43cd-5714-978a-e6cbeb7dddd4
-- title:
--   Residue theorem on a circle for simple poles
-- statement:
--   Let $R$ be a real number with $0 < R$, let $z_0 \in \mathbb{C}$, let $h, c : \mathbb{C} \to \mathbb{C}$ be functions and let $Z$ be a finite subset of $\mathbb{C}$. Assume: every $a \in Z$ lies in the open ball of radius $R$ about $z_0$; $h$ is analytic at each point $z$ of the closed ball of radius $R$ about $z_0$ with $z \notin Z$; and for each $a \in Z$ there exists $g : \mathbb{C} \to \mathbb{C}$, analytic at $a$, such that $h(z) = c(a)/(z-a) + g(z)$ holds for all $z$ in some punctured neighbourhood of $a$ (eventually in the filter $\mathcal{N}[\neq] a$). Then the circle integral of $h$ over the circle of centre $z_0$ and radius $R$ equals $2\pi i \sum_{a \in Z} c(a)$. Note that the values $c(a)$ for $a \notin Z$ are unconstrained and do not enter the conclusion, and that only the existence of the simple-pole expansion with coefficient $c(a)$ is assumed, not that $h$ actually fails to be analytic at $a$.
--
--   This is the residue theorem for a circular contour, in the special case of finitely many poles of order at most one, the residue at $a$ being prescribed by the assumed expansion. It is used for circle integrals of logarithmic-derivative type, being cited by [`Complex.circleIntegral_div_sub_eq_sum_div_deriv`](thm.html#Complex.circleIntegral_div_sub_eq_sum_div_deriv), [`Complex.circleIntegral_mul_deriv_div_sub_eq_sum_analyticOrderNatAt`](thm.html#Complex.circleIntegral_mul_deriv_div_sub_eq_sum_analyticOrderNatAt) and, through these, by the period-lattice statement [`AlgebraicCurve.eventually_abelJacobiDiv_fibre_sub_mem_pathPeriodLattice`](thm.html#AlgebraicCurve.eventually_abelJacobiDiv_fibre_sub_mem_pathPeriodLattice).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_circleIntegral_eq_sum_residue_of_simplePole.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology

theorem Complex.circleIntegral_eq_sum_residue_of_simplePole
    {R : ℝ} {z₀ : ℂ} (hR : 0 < R) (h c : ℂ → ℂ) (Z : Finset ℂ)
    (hZ : ∀ a ∈ Z, a ∈ Metric.ball z₀ R)
    (hh : ∀ z ∈ Metric.closedBall z₀ R, z ∉ Z → AnalyticAt ℂ h z)
    (hloc : ∀ a ∈ Z, ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      ∀ᶠ z in 𝓝[≠] a, h z = c a / (z - a) + g z) :
    (∮ z in C(z₀, R), h z) = 2 * Real.pi * Complex.I * ∑ a ∈ Z, c a := by sorry
