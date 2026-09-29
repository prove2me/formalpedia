-- Prove2me | Theorems.Thm_Complex_hasDerivAt_circleIntegral_mul_deriv_div_sub
-- name    : Complex.hasDerivAt_circleIntegral_mul_deriv_div_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/9b324b38-7850-5826-b0b1-3826b7eabc9e
-- title:
--   Holomorphic dependence on t of oint G Φ'/(Φ-t)
-- statement:
--   Let $\Phi, G : \mathbb{C} \to \mathbb{C}$ be functions, let $z_0, t_0 \in \mathbb{C}$, and let $r$ be a real number with $0 < r$. Assume that $\Phi$ is analytic at every point $z$ of the circle $\{z : |z - z_0| = r\}$ (the metric sphere of centre $z_0$ and radius $r$ in $\mathbb{C}$), that $G$ is likewise analytic at every point of that circle, and that $\Phi(z) \neq t_0$ for every $z$ on the circle. The conclusion is a statement of complex differentiability in the parameter $t$: the function
--   $$t \longmapsto \oint_{C(z_0,r)} G(z)\,\frac{\Phi'(z)}{\Phi(z) - t}\,dz,$$
--   where the circle integral is the usual parametrised integral over the circle of centre $z_0$ and radius $r$ and $\Phi'$ denotes the derivative of $\Phi$, has at the point $t = t_0$ the complex derivative
--   $$\oint_{C(z_0,r)} \frac{G'(z)}{\Phi(z) - t_0}\,dz.$$
--   No analyticity or regularity of $\Phi$ or $G$ is assumed away from the circle, and the asserted value of the derivative is the integral of $G'/(\Phi - t_0)$ rather than the form $G\,\Phi'/(\Phi - t_0)^2$ produced by naive differentiation under the integral sign; the two agree because their difference is the integral of an exact derivative around a closed curve.
--
--   This is the holomorphy of a circle integral in the level parameter $t$, in the shape needed for weighted fibre traces: combined with the argument principle it shows that $t \mapsto \sum_{\Phi(z) = t} m_z G(z)$ is holomorphic and identifies its derivative. It is used in the study of fibre sums for the Abel–Jacobi map, in [`AlgebraicCurve.eventually_abelJacobiDiv_fibre_sub_mem_pathPeriodLattice`](thm.html#AlgebraicCurve.eventually_abelJacobiDiv_fibre_sub_mem_pathPeriodLattice), [`AlgebraicCurve.exists_ball_abelJacobiDiv_correspondence_sub_sub_mem_pathPeriodLattice`](thm.html#AlgebraicCurve.exists_ball_abelJacobiDiv_correspondence_sub_sub_mem_pathPeriodLattice) and [`ModularCurve.eventually_abelFibreSumOf_sub_mem_periodLatticeOf`](thm.html#ModularCurve.eventually_abelFibreSumOf_sub_mem_periodLatticeOf).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_hasDerivAt_circleIntegral_mul_deriv_div_sub.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Real

theorem Complex.hasDerivAt_circleIntegral_mul_deriv_div_sub
    {Φ G : ℂ → ℂ} {z₀ t₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hΦ : ∀ z ∈ Metric.sphere z₀ r, AnalyticAt ℂ Φ z)
    (hG : ∀ z ∈ Metric.sphere z₀ r, AnalyticAt ℂ G z)
    (hne : ∀ z ∈ Metric.sphere z₀ r, Φ z ≠ t₀) :
    HasDerivAt (fun t : ℂ => ∮ z in C(z₀, r), G z * deriv Φ z / (Φ z - t))
      (∮ z in C(z₀, r), deriv G z / (Φ z - t₀)) t₀ := by sorry
