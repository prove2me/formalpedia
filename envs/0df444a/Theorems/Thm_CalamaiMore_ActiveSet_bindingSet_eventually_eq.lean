-- Prove2me | Theorems.Thm_CalamaiMore_ActiveSet_bindingSet_eventually_eq
-- name    : CalamaiMore.ActiveSet.bindingSet_eventually_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:56:47.949677+00:00
-- url     : https://prove2.me/theorems/cea0413f-7964-44fb-b2ec-6c9bdd55eff5
-- title:
--   Theorem 4.2 — the binding set is identified in finitely many steps
-- statement:
--   Let $\Omega = \{x \in E : \langle c_j, x \rangle \ge \delta_j,\ j = 1, \dots, m\}$ be a polyhedral set in a finite-dimensional real inner product space $E$ with active sets $A(x)$, and let $f : E \to \mathbb{R}$ be continuously differentiable on $\Omega$. Let $\lambda(\cdot)$ be a consistent Lagrange multiplier estimate, with binding sets $B(x) = \{j \in A(x) : \lambda_j(x) \ge 0\}$, whose value at $x^*$ is the Kuhn–Tucker multiplier vector:
--
--   $$
--   \nabla f(x^*) = \sum_{j \in A(x^*)} \lambda_j(x^*)\, c_j .
--   $$
--
--   Let $\{x_k\}$ be an arbitrary sequence in $\Omega$ converging to $x^*$. If $\|\nabla_\Omega f(x_k)\| \to 0$ and $x^*$ is nondegenerate, then
--
--   $$
--   B(x_k) = B(x^*) \quad \text{for all } k \text{ sufficiently large.}
--   $$
--
--   An algorithm that uses a multiplier estimate to decide which constraints to keep therefore makes the right decision after finitely many iterations.
--
--   **Formalization Note** The displayed condition on $\lambda(x^*)$ is implicit in the source, which writes $\lambda(x^*)$ for the Kuhn–Tucker multipliers of (4.3) (as the least-squares estimate (4.5) gives). Without it the statement is false: a consistent estimate may have $\lambda_j(x^*) = 0$ while $\lambda_j(x_k)$ alternates in sign. By linear independence it makes $\lambda_j(x^*) = \lambda^*_j > 0$ on $A(x^*)$.
-- source:
--   Calamai & Moré, Projected gradient methods for linearly constrained problems, Math. Programming 39 (1987), p. 107, Theorem 4.2 (with Eq. (4.4) and the Definition of a consistent estimate)

import Mathlib
import Definitions.Def_CalamaiMore_ActiveSet_projGrad
import Definitions.Def_CalamaiMore_ActiveSet_bindingSet

namespace CalamaiMore.ActiveSet

/-- Calamai–Moré, Theorem 4.2 (p. 107): let `Ω` be the polyhedral set of (4.1), `f` continuously
differentiable on `Ω`, and `{x_k}` an arbitrary sequence in `Ω` converging to `x*`. If the binding
sets (4.4) are defined by a consistent multiplier estimate `λ(·)` whose value at `x*` is the
Kuhn–Tucker multiplier vector of (4.3) (`∇f(x*) = ∑_{j ∈ A(x*)} λ_j(x*) c_j`, the hypothesis the
paper leaves implicit), if `‖∇_Ω f(x_k)‖ → 0`, and if `x*` is nondegenerate, then
`B(x_k) = B(x*)` for all `k` sufficiently large. -/
theorem bindingSet_eventually_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {m : ℕ} (c : Fin m → E) (δ : Fin m → ℝ)
    (f : E → ℝ) (hfd : ∀ x ∈ polyhedron c δ, DifferentiableAt ℝ f x)
    (hfc : ContinuousOn (gradient f) (polyhedron c δ))
    (lam : E → Fin m → ℝ) (hcons : IsConsistentEstimate c δ f lam)
    (x : ℕ → E) (xs : E) (hx : ∀ k, x k ∈ polyhedron c δ)
    (hlim : Filter.Tendsto x Filter.atTop (nhds xs))
    (hpg : Filter.Tendsto (fun k => ‖projGrad f (polyhedron c δ) (x k)‖) Filter.atTop (nhds 0))
    (hnd : IsNondegenerate c δ f xs)
    (hlamxs : gradient f xs = ∑ j ∈ activeSet c δ xs, lam xs j • c j) :
    ∀ᶠ k in Filter.atTop, bindingSet c δ lam (x k) = bindingSet c δ lam xs := by sorry

end CalamaiMore.ActiveSet
