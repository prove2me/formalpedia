-- Prove2me | Theorems.Thm_CalamaiMore_ActiveSet_activeSet_eventually_eq
-- name    : CalamaiMore.ActiveSet.activeSet_eventually_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:56:00.759785+00:00
-- url     : https://prove2.me/theorems/07bf9ba6-04e1-4100-8e7a-01e15f66e995
-- title:
--   Theorem 4.1 — the active set is identified in finitely many steps at a nondegenerate point
-- statement:
--   Let $\Omega = \{x \in E : \langle c_j, x \rangle \ge \delta_j,\ j = 1, \dots, m\}$ be a polyhedral set in a finite-dimensional real inner product space $E$, with active sets $A(x) = \{j : \langle c_j, x \rangle = \delta_j\}$, and let $f : E \to \mathbb{R}$ be continuously differentiable on $\Omega$. Let $\{x_k\}$ be an arbitrary sequence in $\Omega$ converging to $x^*$, and let $\nabla_\Omega f$ be the projected gradient. If
--
--   $$
--   \lim_{k \to \infty} \|\nabla_\Omega f(x_k)\| = 0
--   $$
--
--   and $x^*$ is nondegenerate (the active normals $\{c_j : j \in A(x^*)\}$ are linearly independent and $\nabla f(x^*) = \sum_{j \in A(x^*)} \lambda^*_j c_j$ with every $\lambda^*_j > 0$), then
--
--   $$
--   A(x_k) = A(x^*) \quad \text{for all } k \text{ sufficiently large.}
--   $$
--
--   The result does not depend on how the sequence is generated: any method whose iterates stay feasible, converge, and drive the projected gradient to zero identifies the optimal active set after finitely many iterations, after which it behaves like a method for an equality-constrained problem.
--
--   **Formalization Note** The constraints are indexed by `Fin m`; "for all $k$ sufficiently large" is `∀ᶠ k in atTop`, and the conclusion is equality of finite sets of indices, not inclusion.
-- source:
--   Calamai & Moré, Projected gradient methods for linearly constrained problems, Math. Programming 39 (1987), p. 106, Theorem 4.1

import Mathlib
import Definitions.Def_CalamaiMore_ActiveSet_projGrad
import Definitions.Def_CalamaiMore_ActiveSet_IsNondegenerate

namespace CalamaiMore.ActiveSet

/-- Calamai–Moré, Theorem 4.1 (p. 106): let `Ω = {x : ⟨c_j, x⟩ ≥ δ_j, j = 1, …, m}` be
polyhedral, `f` continuously differentiable on `Ω`, and `{x_k}` an arbitrary sequence in `Ω`
converging to `x*`. If `‖∇_Ω f(x_k)‖ → 0` and `x*` is nondegenerate, then
`A(x_k) = A(x*)` for all `k` sufficiently large. -/
theorem activeSet_eventually_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {m : ℕ} (c : Fin m → E) (δ : Fin m → ℝ)
    (f : E → ℝ) (hfd : ∀ x ∈ polyhedron c δ, DifferentiableAt ℝ f x)
    (hfc : ContinuousOn (gradient f) (polyhedron c δ))
    (x : ℕ → E) (xs : E) (hx : ∀ k, x k ∈ polyhedron c δ)
    (hlim : Filter.Tendsto x Filter.atTop (nhds xs))
    (hpg : Filter.Tendsto (fun k => ‖projGrad f (polyhedron c δ) (x k)‖) Filter.atTop (nhds 0))
    (hnd : IsNondegenerate c δ f xs) :
    ∀ᶠ k in Filter.atTop, activeSet c δ (x k) = activeSet c δ xs := by sorry

end CalamaiMore.ActiveSet
