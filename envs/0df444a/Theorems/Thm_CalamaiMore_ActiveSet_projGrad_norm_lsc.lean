-- Prove2me | Theorems.Thm_CalamaiMore_ActiveSet_projGrad_norm_lsc
-- name    : CalamaiMore.ActiveSet.projGrad_norm_lsc
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:54:05.128903+00:00
-- url     : https://prove2.me/theorems/82e9ef0e-0b43-4815-b140-49eb20ffc905
-- title:
--   Lemma 3.3 — $\|\nabla_\Omega f(\cdot)\|$ is lower semicontinuous on $\Omega$
-- statement:
--   Let $\Omega$ be a nonempty closed convex subset of a finite-dimensional real inner product space $E$, and let $f : E \to \mathbb{R}$ be continuously differentiable on $\Omega$. Then the map
--
--   $$
--   x \mapsto \|\nabla_\Omega f(x)\|
--   $$
--
--   is lower semicontinuous on $\Omega$: for every sequence $\{x_k\} \subseteq \Omega$ converging to $x \in \Omega$, $\|\nabla_\Omega f(x)\| \le \liminf_k \|\nabla_\Omega f(x_k)\|$.
--
--   The projected gradient itself need not be continuous, since the tangent cone jumps when the point reaches a new face of $\Omega$; lower semicontinuity of its norm is what survives, and it is what shows that the limit of a sequence with $\|\nabla_\Omega f(x_k)\| \to 0$ is stationary.
--
--   **Formalization Note** Lower semicontinuity on $\Omega$ is Mathlib's `LowerSemicontinuousOn`, i.e. relative to $\Omega$.
-- source:
--   Calamai & Moré, Projected gradient methods for linearly constrained problems, Math. Programming 39 (1987), p. 104, Lemma 3.3

import Mathlib
import Definitions.Def_CalamaiMore_ActiveSet_projGrad

namespace CalamaiMore.ActiveSet

/-- Calamai–Moré, Lemma 3.3 (p. 104): for `Ω` nonempty closed convex and `f` continuously
differentiable on `Ω`, the map `x ↦ ‖∇_Ω f(x)‖` is lower semicontinuous on `Ω`. -/
theorem projGrad_norm_lsc {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (Ω : Set E) (hΩne : Ω.Nonempty) (hΩc : IsClosed Ω) (hΩcv : Convex ℝ Ω)
    (f : E → ℝ) (hfd : ∀ x ∈ Ω, DifferentiableAt ℝ f x) (hfc : ContinuousOn (gradient f) Ω) :
    LowerSemicontinuousOn (fun y => ‖projGrad f Ω y‖) Ω := by sorry

end CalamaiMore.ActiveSet
