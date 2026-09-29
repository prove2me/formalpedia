-- Prove2me | Theorems.Thm_Complex_circleIntegral_mul_deriv_div_sub_eq_sum_analyticOrderNatAt
-- name    : Complex.circleIntegral_mul_deriv_div_sub_eq_sum_analyticOrderNatAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/ce9dc355-fa99-5c5e-af90-5119e18d13b5
-- title:
--   Weighted argument principle on a disc
-- statement:
--   Let $R,G\colon\mathbb{C}\to\mathbb{C}$ be functions, $z_0,t\in\mathbb{C}$ and $r\in\mathbb{R}$ with $r>0$. Assume that $R$ is analytic at every point of the closed disc $\{z:|z-z_0|\le r\}$, that $G$ is analytic at every point of that same closed disc, and that $R(z)\neq t$ for every $z$ on the circle $|z-z_0|=r$. The conclusion asserts the existence of a finite set $Z\subseteq\mathbb{C}$ (a `Finset`) whose members are exactly the points $a$ with $|a-z_0|<r$ and $R(a)=t$ — so in particular the solution set of $R=t$ in the open disc is finite — and for which the circle integral of $G(z)\,R'(z)/(R(z)-t)$ over the circle of centre $z_0$ and radius $r$, with $R'$ the Mathlib derivative `deriv R`, equals
--   $$2\pi i\sum_{a\in Z}\operatorname{ord}_a(R-t)\,G(a),$$
--   where $\operatorname{ord}_a(R-t)$ denotes `analyticOrderNatAt (fun z => R z - t) a`, the order of vanishing at $a$ of $z\mapsto R(z)-t$ as a natural number, cast into $\mathbb{C}$.
--
--   This is the argument principle with an analytic weight $G$: for $G=1$ it counts the solutions of $R=t$ in the disc with multiplicity, and in general it expresses the symmetric sum $\sum_{R(a)=t}\operatorname{ord}_a(R-t)G(a)$ over a fibre of $R$ as a contour integral, hence as a function of $t$ depending analytically on the parameters. It is used in the analytic theory of the Abel–Jacobi map on an algebraic curve, in the statements [`AlgebraicCurve.eventually_abelJacobiDiv_fibre_sub_mem_pathPeriodLattice`](thm.html#AlgebraicCurve.eventually_abelJacobiDiv_fibre_sub_mem_pathPeriodLattice) and [`AlgebraicCurve.exists_ball_abelJacobiDiv_correspondence_sub_sub_mem_pathPeriodLattice`](thm.html#AlgebraicCurve.exists_ball_abelJacobiDiv_correspondence_sub_sub_mem_pathPeriodLattice).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_circleIntegral_mul_deriv_div_sub_eq_sum_analyticOrderNatAt.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Real

theorem Complex.circleIntegral_mul_deriv_div_sub_eq_sum_analyticOrderNatAt
    {R G : ℂ → ℂ} {z₀ t : ℂ} {r : ℝ} (hr : 0 < r)
    (hR : ∀ z ∈ Metric.closedBall z₀ r, AnalyticAt ℂ R z)
    (hG : ∀ z ∈ Metric.closedBall z₀ r, AnalyticAt ℂ G z)
    (hne : ∀ z ∈ Metric.sphere z₀ r, R z ≠ t) :
    ∃ Z : Finset ℂ, (∀ a, a ∈ Z ↔ a ∈ Metric.ball z₀ r ∧ R a = t) ∧
      (∮ z in C(z₀, r), G z * deriv R z / (R z - t)) =
        2 * π * Complex.I *
          ∑ a ∈ Z, (analyticOrderNatAt (fun z => R z - t) a : ℂ) * G a := by sorry
