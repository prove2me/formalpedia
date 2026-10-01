-- Prove2me | Theorems.Thm_CalamaiMore_ActiveSet_stationary_iff_kuhnTucker
-- name    : CalamaiMore.ActiveSet.stationary_iff_kuhnTucker
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:55:13.535035+00:00
-- url     : https://prove2.me/theorems/67c21a13-d5c0-48a3-aed3-e0dbb73e30c8
-- title:
--   Eq. (4.3) — stationary points of a polyhedral problem are Kuhn–Tucker points
-- statement:
--   Let $\Omega = \{x \in E : \langle c_j, x \rangle \ge \delta_j,\ j = 1, \dots, m\}$ be a polyhedral set in a finite-dimensional real inner product space $E$, and let $f : E \to \mathbb{R}$ be continuously differentiable on $\Omega$. A point $x^* \in \Omega$ is a stationary point of $\min\{f(x) : x \in \Omega\}$, i.e. $\langle \nabla f(x^*), x - x^* \rangle \ge 0$ for all $x \in \Omega$, if and only if it is a Kuhn–Tucker point:
--
--   $$
--   \nabla f(x^*) = \sum_{j \in A(x^*)} \lambda^*_j c_j, \qquad \lambda^*_j \ge 0 \text{ for } j \in A(x^*).
--   $$
--
--   For linear constraints no constraint qualification is needed: the first-order condition always has a multiplier representation over the active constraints.
--
--   **Formalization Note** "Continuously differentiable on $\Omega$" is the standing assumption of §4, stated as `∀ x ∈ Ω, DifferentiableAt ℝ f x` and `ContinuousOn (gradient f) Ω`.
-- source:
--   Calamai & Moré, Projected gradient methods for linearly constrained problems, Math. Programming 39 (1987), p. 106, Eq. (4.3)

import Mathlib
import Definitions.Def_CalamaiMore_Shared_IsStationaryPoint
import Definitions.Def_CalamaiMore_ActiveSet_IsNondegenerate

namespace CalamaiMore.ActiveSet

/-- Calamai–Moré, Eq. (4.3) (p. 106): for the polyhedral set `Ω` of (4.1) and `f` continuously
differentiable on `Ω`, a point `x ∈ Ω` is a stationary point of `min {f(x) : x ∈ Ω}` if and only
if it is a Kuhn–Tucker point, `∇f(x) = ∑_{j ∈ A(x)} λ_j c_j` with `λ_j ≥ 0`. -/
theorem stationary_iff_kuhnTucker {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {m : ℕ} (c : Fin m → E) (δ : Fin m → ℝ)
    (f : E → ℝ) (hfd : ∀ x ∈ polyhedron c δ, DifferentiableAt ℝ f x)
    (hfc : ContinuousOn (gradient f) (polyhedron c δ))
    (x : E) (hx : x ∈ polyhedron c δ) :
    CalamaiMore.Shared.IsStationaryPoint f (polyhedron c δ) x ↔ IsKuhnTuckerPoint c δ f x := by sorry

end CalamaiMore.ActiveSet
