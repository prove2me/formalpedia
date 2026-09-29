-- Prove2me | Theorems.Thm_CalamaiMore_Convergence_projGrad_norm_lsc
-- name    : CalamaiMore.Convergence.projGrad_norm_lsc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:34:23.26251+00:00
-- url     : https://prove2.me/theorems/80b69adc-c7e7-4818-b4c1-b53dcbfdd07a
-- title:
--   Lemma 3.3 — $\|\nabla_\Omega f(\cdot)\|$ is lower semicontinuous on $\Omega$
-- statement:
--   Let $\Omega$ be a nonempty closed convex subset of a finite-dimensional real inner product space $E$ and let $f : E \to \mathbb R$ be continuously differentiable on $\Omega$. Then the map
--
--   $$
--   x \mapsto \|\nabla_\Omega f(x)\|
--   $$
--
--   is lower semicontinuous on $\Omega$: if $x_k \to x$ with all $x_k, x \in \Omega$, then $\|\nabla_\Omega f(x)\| \le \liminf_{k} \|\nabla_\Omega f(x_k)\|$.
--
--   The map need not be continuous: $\nabla_\Omega f$ can be bounded away from zero near a stationary point. Lower semicontinuity is what transfers $\|\nabla_\Omega f(x_k)\| \to 0$ to stationarity of limit points.
--
--   **Formalization Note** Lower semicontinuity on $\Omega$ is Mathlib's `LowerSemicontinuousOn`, i.e. relative to $\Omega$.
-- source:
--   Calamai & Moré, Projected gradient methods for linearly constrained problems, Math. Programming 39 (1987), p. 104, Lemma 3.3

import Mathlib
import Definitions.Def_CalamaiMore_Convergence_projGrad

namespace CalamaiMore.Convergence

/-- Calamai–Moré, Lemma 3.3 (p. 104): `x ↦ ‖∇_Ω f(x)‖` is lower semicontinuous on `Ω`. -/
theorem projGrad_norm_lsc {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Ω : Set E) (hΩne : Ω.Nonempty) (hΩc : IsClosed Ω) (hΩcv : Convex ℝ Ω)
    (f : E → ℝ) (hfd : ∀ x ∈ Ω, DifferentiableAt ℝ f x) (hfc : ContinuousOn (gradient f) Ω) :
    LowerSemicontinuousOn (fun y => ‖projGrad f Ω y‖) Ω := by sorry

end CalamaiMore.Convergence
