-- Prove2me | Theorems.Thm_Complex_circleIntegral_div_sub_eq_sum_div_deriv
-- name    : Complex.circleIntegral_div_sub_eq_sum_div_deriv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/dbe3c56b-6f9a-57b0-a2f4-9c7880de7ee5
-- title:
--   Circle integral of Ψ/(R-t) over simple solutions of R=t
-- statement:
--   Let $R,\Psi:\mathbb{C}\to\mathbb{C}$ be functions, $c,t\in\mathbb{C}$ and $r$ a real number with $r>0$. Assume $R$ is analytic at every point of the closed ball $\overline{B}(c,r)$, that $\Psi$ is likewise analytic at every point of $\overline{B}(c,r)$, and that $R(z)\neq t$ for every $z$ on the circle $|z-c|=r$. Let $Z$ be a finite subset of $\mathbb{C}$ whose membership is characterised exactly: for every $a$, one has $a\in Z$ if and only if $a$ lies in the open ball $B(c,r)$ and $R(a)=t$ (so $Z$ is precisely the solution set of $R=t$ in the open disc, the hypothesis in particular asserting that this set is finite). Assume finally that $\operatorname{deriv} R\,(a)\neq 0$ for every $a\in Z$, i.e. each such solution is simple. Then the circle integral of $z\mapsto \Psi(z)/(R(z)-t)$ over the circle of centre $c$ and radius $r$ equals $2\pi i \sum_{a\in Z}\Psi(a)/\operatorname{deriv} R\,(a)$.
--
--   This is the residue formula for the weighted counting integrals attached to a holomorphic map at an unramified value: each simple solution of $R=t$ contributes a simple pole of $\Psi/(R-t)$ with residue $\Psi(a)/R'(a)$. It is used in the construction of local sections of Abel–Jacobi type maps, in [`AlgebraicCurve.exists_ball_abelJacobiDiv_correspondence_sub_sub_mem_pathPeriodLattice`](thm.html#AlgebraicCurve.exists_ball_abelJacobiDiv_correspondence_sub_sub_mem_pathPeriodLattice).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_circleIntegral_div_sub_eq_sum_div_deriv.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Complex.circleIntegral_div_sub_eq_sum_div_deriv {R Ψ : ℂ → ℂ} {c t : ℂ} {r : ℝ}
    (hr : 0 < r) (hR : ∀ z ∈ Metric.closedBall c r, AnalyticAt ℂ R z)
    (hΨ : ∀ z ∈ Metric.closedBall c r, AnalyticAt ℂ Ψ z)
    (hne : ∀ z ∈ Metric.sphere c r, R z ≠ t) (Z : Finset ℂ)
    (hZ : ∀ a, a ∈ Z ↔ a ∈ Metric.ball c r ∧ R a = t) (hsimple : ∀ a ∈ Z, deriv R a ≠ 0) :
    (∮ z in C(c, r), Ψ z / (R z - t)) =
      2 * Real.pi * Complex.I * ∑ a ∈ Z, Ψ a / deriv R a := by sorry
