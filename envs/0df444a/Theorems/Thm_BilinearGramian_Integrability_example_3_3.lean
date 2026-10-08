-- Prove2me | Theorems.Thm_BilinearGramian_Integrability_example_3_3
-- name    : BilinearGramian.Integrability.example_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:39:11.730882+00:00
-- url     : https://prove2.me/theorems/60fc8ed7-a57c-4ecd-8853-4b9f79338b01
-- title:
--   Example 3.3 — a locally controllable bilinear system for which x ↦ P̃(x)⁻¹x is not a gradient near 0, so (3.8) fails
-- statement:
--   Consider the single-input bilinear system of Example 3.3,
--   $$\dot x = Ax + Nx\,u + b\,u, \qquad A = \begin{bmatrix} -1 & 0 \\ 0 & -2 \end{bmatrix}, \quad N = \nu \begin{bmatrix} 0 & 1 \\ 1 & 0 \end{bmatrix}, \quad b = \begin{bmatrix} 1 \\ 1 \end{bmatrix},$$
--   with a real parameter $\nu \neq 0$. For every $x \in \mathbb R^2$ let $\tilde P(x)$ be the solution of the Lyapunov equation (3.9),
--   $$A \tilde P(x) + \tilde P(x) A^T = -(Nx + b)(Nx + b)^T .$$
--   Then:
--
--   1. the system is locally controllable, i.e. the pair $(A, b)$ is controllable;
--   2. for every $\varepsilon > 0$ there is **no** function $E : \mathbb R^2 \to \mathbb R$ such that
--   $$\nabla E(x) = \tilde P(x)^{-1} x \qquad \text{for all } x \text{ with } 0 < \|x\| < \varepsilon .$$
--
--   In words: the vector field $x \mapsto \tilde P(x)^{-1}x$ is not integrable on any punctured neighbourhood of the origin. In particular the formula $\nabla E_c(x) = \tilde P(x)^{-1}x$ of (3.8), claimed in the literature for the controllability energy functional $E_c$ of a locally controllable bilinear system "for $x \neq 0$ with $\|x\|$ sufficiently small", cannot hold for this system.
--
--   **Formalization Note** The statement refutes every candidate potential $E$, which is exactly "not integrable", and so does not need the definition of $E_c$. $E$ is only required to be differentiable, with the given gradient, at the points of the punctured ball. $\nu \neq 0$ is added: at $\nu = 0$ the Gramian $\tilde P(x)$ is a constant symmetric matrix and the field is a gradient, whereas the paper calls $\nu$ "irrelevant for the computation". $\tilde P$ is any function satisfying (3.9) at every point; since $A$ is stable there is exactly one. The plane is `EuclideanSpace ℝ (Fin 2)` so that the gradient is the Euclidean one. `(Pt x)⁻¹` is Mathlib's matrix inverse, which is $0$ at singular matrices; $\tilde P(x)$ is invertible near the origin, so this value does not enter. The analogous claim for the observability Gramian $\tilde Q$, which the paper says can be argued similarly, is not part of this statement.
-- source:
--   Benner, Damm, Lyapunov Equations, Energy Functionals, and Model Order Reduction of Bilinear and Stochastic Systems, SIAM J. Control Optim. 49(2) (2011), pp. 697–698, Example 3.3

import Mathlib
import Definitions.Def_BilinearGramian_Integrability_LinGramian
import Definitions.Def_BilinearGramian_Integrability_Example33

open Matrix

namespace BilinearGramian.Integrability

/-- Example 3.3 (Benner–Damm 2011, pp. 697–698). For the single-input bilinear system with
`A = diag(-1, -2)`, `N = ν [0 1; 1 0]` (`ν ≠ 0`), `b = (1, 1)ᵀ`: the system is locally
controllable (`(A, b)` controllable), and if `P̃(x)` is defined by (3.9) for every `x`, then on no
punctured ball `0 < ‖x‖ < ε` is the field `x ↦ P̃(x)⁻¹ x` the gradient of a real function `E`;
so (3.8), `∇E_c(x) = P̃(x)⁻¹ x` for `x ≠ 0` with `‖x‖` sufficiently small, cannot hold. -/
theorem example_3_3 (ν : ℝ) (hν : ν ≠ 0) (Pt : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ)
    (hPt : ∀ x, IsLinGramian exA (fun _ : Fin 1 => exN ν) exB x (Pt x)) :
    IsControllable exA exB ∧
      ∀ ε > 0, ¬ ∃ E : EuclideanSpace ℝ (Fin 2) → ℝ,
        ∀ x : EuclideanSpace ℝ (Fin 2), 0 < ‖x‖ → ‖x‖ < ε →
          HasGradientAt E (WithLp.toLp 2 ((Pt x.ofLp)⁻¹ *ᵥ x.ofLp)) x := by sorry

end BilinearGramian.Integrability
