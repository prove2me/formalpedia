-- Prove2me | Theorems.Thm_ArmijoGrad_Conv_tendsto_of_gradient_tendsto_zero
-- name    : ArmijoGrad.Conv.tendsto_of_gradient_tendsto_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:02:51.782595+00:00
-- url     : https://prove2.me/theorems/4209094f-7f1d-4833-9421-f4a7b0f9a272
-- title:
--   §2, proof of the THEOREM, p. 2 — under Condition IV, y_k ∈ S(x₀) and |∇f(y_k)| → 0 imply y_k → x*
-- statement:
--   Let $f : E^n \to \mathbb{R}$ satisfy Condition IV at $x_0$ for the minimizer $x^*$: $f \in C^1$ on $S(x_0)$, $f(x^*) = \inf_{E^n} f$, and for every $r > 0$ the infimum $m(r)$ of $|\nabla f|$ over $\{x \in S(x_0) : |x - x^*| \ge r\}$ is positive ($m(r) = \infty$ if that set is empty). Then every sequence $\{y_k\}$ in $S(x_0)$ with $|\nabla f(y_k)| \to 0$ satisfies
--   $$y_k \to x^* \qquad (k \to \infty).$$
--
--   This is the content of the sentence "The remainder of the theorem follows from Condition IV" in the proof of the convergence theorem.
--
--   **Formalization Note** Only Condition IV is used; the other standing assumptions are omitted. $m(r) > 0$ is encoded as the existence of a positive lower bound for $|\nabla f|$ on the set, so the empty-set convention $m(r) = \infty$ is respected.
-- source:
--   Armijo, Minimization of functions having Lipschitz continuous first partial derivatives, Pacific J. Math. 16 (1966), p. 2, §2, proof of the THEOREM, last sentence

import Mathlib
import Definitions.Def_ArmijoGrad_Conv_Setting

open Filter Topology

namespace ArmijoGrad.Conv

/-- §2, proof of the THEOREM, p. 2 ("The remainder of the theorem follows from Condition IV"):
under Condition IV, a sequence in `S(x₀)` along which `|∇f| → 0` converges to `x*`. -/
theorem tendsto_of_gradient_tendsto_zero {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x0 xstar : EuclideanSpace ℝ (Fin n)) (hIV : ConditionIV f x0 xstar) :
    ∀ y : ℕ → EuclideanSpace ℝ (Fin n), (∀ k, y k ∈ levelSet f x0) →
      Tendsto (fun k => ‖gradient f (y k)‖) atTop (𝓝 0) → Tendsto y atTop (𝓝 xstar) := by sorry

end ArmijoGrad.Conv
