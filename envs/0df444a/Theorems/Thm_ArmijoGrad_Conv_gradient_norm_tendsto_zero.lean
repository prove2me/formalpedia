-- Prove2me | Theorems.Thm_ArmijoGrad_Conv_gradient_norm_tendsto_zero
-- name    : ArmijoGrad.Conv.gradient_norm_tendsto_zero
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:02:38.444005+00:00
-- url     : https://prove2.me/theorems/61f9d312-2391-4bbb-ab9f-406f3cb3c19f
-- title:
--   §2, proof of the THEOREM, p. 2 — for x_{k+1} ∈ S*(x_k, δ) and f bounded below, |∇f(x_k)| → 0
-- statement:
--   Let $f : E^n \to \mathbb{R}$ be bounded below on $E^n$, let $x_0 \in E^n$ and $\delta > 0$, and let $\{x_k\}_{k=0}^\infty$ be a sequence with first term $x_0$ such that $x_{k+1} \in S^*(x_k,\delta)$ for $k = 0, 1, 2, \dots$ Then
--   $$|\nabla f(x_k)| \to 0 \qquad (k \to \infty).$$
--
--   This is the step of the proof that turns sufficient decrease into stationarity; Condition IV then turns stationarity into convergence of the iterates.
--
--   **Formalization Note** Continuity and Conditions III and IV are not needed and are omitted. $\nabla f$ is Mathlib's `gradient`, the same gradient used in the definition of $S^*(x,\delta)$.
-- source:
--   Armijo, Minimization of functions having Lipschitz continuous first partial derivatives, Pacific J. Math. 16 (1966), p. 2, §2, proof of the THEOREM, second sentence

import Mathlib
import Definitions.Def_ArmijoGrad_Conv_Setting

open Filter Topology

namespace ArmijoGrad.Conv

/-- §2, proof of the THEOREM, p. 2: if `f` is bounded below, `x₀` is the first term and
`x_{k+1} ∈ S*(x_k, δ)` for every `k`, then `|∇f(x_k)| → 0`. -/
theorem gradient_norm_tendsto_zero {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hbdd : BddBelow (Set.range f)) (x0 : EuclideanSpace ℝ (Fin n)) (δ : ℝ) (hδ : 0 < δ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx0 : x 0 = x0)
    (hseq : ∀ k, x (k + 1) ∈ sdSet f (x k) δ) :
    Tendsto (fun k => ‖gradient f (x k)‖) atTop (𝓝 0) := by sorry

end ArmijoGrad.Conv
