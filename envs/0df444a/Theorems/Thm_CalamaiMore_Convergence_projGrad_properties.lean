-- Prove2me | Theorems.Thm_CalamaiMore_Convergence_projGrad_properties
-- name    : CalamaiMore.Convergence.projGrad_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:33:08.34826+00:00
-- url     : https://prove2.me/theorems/d03d43ae-583a-4bd9-a57f-834398104614
-- title:
--   Lemma 3.1 — the projected gradient is a steepest descent direction
-- statement:
--   Let $\Omega$ be a nonempty closed convex subset of a finite-dimensional real inner product space $E$, $f : E \to \mathbb R$ continuously differentiable on $\Omega$, $x \in \Omega$, $T(x)$ the tangent cone of $\Omega$ at $x$ and $\nabla_\Omega f(x)$ the projected gradient. Then:
--
--   1. $-\langle \nabla f(x), \nabla_\Omega f(x) \rangle = \|\nabla_\Omega f(x)\|^2$;
--   2. the minimum below is attained and
--   $$
--   \min\{\langle \nabla f(x), v \rangle : v \in T(x),\ \|v\| \le 1\} = -\|\nabla_\Omega f(x)\|;
--   $$
--   3. $x$ is a stationary point of $\min\{f(z) : z \in \Omega\}$ if and only if $\nabla_\Omega f(x) = 0$.
--
--   Part 2 shows that $\nabla_\Omega f(x)$ is a steepest descent direction for $f$ relative to $\Omega$; part 3 makes $\|\nabla_\Omega f(x)\|$ a measure of stationarity.
--
--   **Formalization Note** The minimum of part 2 is stated as `IsLeast` of the set of values $\langle\nabla f(x), v\rangle$, which asserts attainment.
-- source:
--   Calamai & Moré, Projected gradient methods for linearly constrained problems, Math. Programming 39 (1987), p. 102, Lemma 3.1

import Mathlib
import Definitions.Def_CalamaiMore_Convergence_projGrad
import Definitions.Def_CalamaiMore_Shared_IsStationaryPoint

namespace CalamaiMore.Convergence

/-- Calamai–Moré, Lemma 3.1 (p. 102): (a) `-⟨∇f(x), ∇_Ω f(x)⟩ = ‖∇_Ω f(x)‖²`;
(b) `min {⟨∇f(x), v⟩ : v ∈ T(x), ‖v‖ ≤ 1} = -‖∇_Ω f(x)‖` (the minimum is attained);
(c) `x` is a stationary point iff `∇_Ω f(x) = 0`. -/
theorem projGrad_properties {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Ω : Set E) (hΩne : Ω.Nonempty) (hΩc : IsClosed Ω) (hΩcv : Convex ℝ Ω)
    (f : E → ℝ) (hfd : ∀ x ∈ Ω, DifferentiableAt ℝ f x) (hfc : ContinuousOn (gradient f) Ω)
    (x : E) (hx : x ∈ Ω) :
    -inner ℝ (gradient f x) (projGrad f Ω x) = ‖projGrad f Ω x‖ ^ 2 ∧
    IsLeast {r : ℝ | ∃ v ∈ CalamaiMore.Shared.tangentCone Ω x, ‖v‖ ≤ 1 ∧ r = inner ℝ (gradient f x) v}
      (-‖projGrad f Ω x‖) ∧
    (CalamaiMore.Shared.IsStationaryPoint f Ω x ↔ projGrad f Ω x = 0) := by sorry

end CalamaiMore.Convergence
