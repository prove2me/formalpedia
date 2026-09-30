-- Prove2me | Theorems.Thm_CalamaiMore_ActiveSet_projGrad_properties
-- name    : CalamaiMore.ActiveSet.projGrad_properties
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:53:32.356545+00:00
-- url     : https://prove2.me/theorems/d121b9c8-8ef2-44ab-9fc5-76eb49041f2f
-- title:
--   Lemma 3.1 — basic properties of the projected gradient
-- statement:
--   Let $\Omega$ be a nonempty closed convex subset of a finite-dimensional real inner product space $E$, let $f : E \to \mathbb{R}$ be continuously differentiable on $\Omega$, let $x \in \Omega$, and let $\nabla_\Omega f(x)$ be the projected gradient, the point of the tangent cone $T(x)$ nearest to $-\nabla f(x)$. Then:
--
--   1. $$-\langle \nabla f(x), \nabla_\Omega f(x) \rangle = \|\nabla_\Omega f(x)\|^2;$$
--   2. $$\min\{\langle \nabla f(x), v \rangle : v \in T(x),\ \|v\| \le 1\} = -\|\nabla_\Omega f(x)\|,$$ and the minimum is attained;
--   3. $x$ is a stationary point of $\min\{f(x) : x \in \Omega\}$ if and only if $\nabla_\Omega f(x) = 0$.
--
--   Part (b) identifies $-\|\nabla_\Omega f(x)\|$ as the steepest rate of first-order decrease of $f$ along feasible directions of unit length, which is why $\|\nabla_\Omega f\|$ is the natural measure of non-stationarity.
--
--   **Formalization Note** "Continuously differentiable on $\Omega$" is `∀ x ∈ Ω, DifferentiableAt ℝ f x` together with `ContinuousOn (gradient f) Ω` (the standing assumption of §3). The minimum in (b) is `IsLeast` of the set of values, so attainment is part of the statement.
-- source:
--   Calamai & Moré, Projected gradient methods for linearly constrained problems, Math. Programming 39 (1987), p. 102, Lemma 3.1

import Mathlib
import Definitions.Def_CalamaiMore_ActiveSet_projGrad
import Definitions.Def_CalamaiMore_Shared_IsStationaryPoint

namespace CalamaiMore.ActiveSet

/-- Calamai–Moré, Lemma 3.1 (p. 102), under the standing assumptions of §3 (`Ω` nonempty closed
convex, `f` continuously differentiable on `Ω`), at `x ∈ Ω`:
(a) `-⟨∇f(x), ∇_Ω f(x)⟩ = ‖∇_Ω f(x)‖²`;
(b) `min {⟨∇f(x), v⟩ : v ∈ T(x), ‖v‖ ≤ 1} = -‖∇_Ω f(x)‖` (the minimum is attained);
(c) `x` is a stationary point iff `∇_Ω f(x) = 0`. -/
theorem projGrad_properties {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (Ω : Set E) (hΩne : Ω.Nonempty) (hΩc : IsClosed Ω) (hΩcv : Convex ℝ Ω)
    (f : E → ℝ) (hfd : ∀ x ∈ Ω, DifferentiableAt ℝ f x) (hfc : ContinuousOn (gradient f) Ω)
    (x : E) (hx : x ∈ Ω) :
    -inner ℝ (gradient f x) (projGrad f Ω x) = ‖projGrad f Ω x‖ ^ 2 ∧
    IsLeast {r : ℝ | ∃ v ∈ CalamaiMore.Shared.tangentCone Ω x, ‖v‖ ≤ 1 ∧ r = inner ℝ (gradient f x) v}
      (-‖projGrad f Ω x‖) ∧
    (CalamaiMore.Shared.IsStationaryPoint f Ω x ↔ projGrad f Ω x = 0) := by sorry

end CalamaiMore.ActiveSet
