-- Prove2me | Theorems.Thm_BilinearGramian_Integrability_jacobian_not_symm
-- name    : BilinearGramian.Integrability.jacobian_not_symm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:39:27.425081+00:00
-- url     : https://prove2.me/theorems/db506b71-356d-41ee-aba1-8b88205ef182
-- title:
--   Example 3.3, p. 698 — F′(ξ(1,1)ᵀ) = P̃⁻¹ + 12νξ/(1 + νξ)³ [2 −1; −4 2] is not symmetric
-- statement:
--   Let $A, N = N(\nu), b$ be the data of Example 3.3, let $\tilde P(x)$ solve (3.9) for every $x \in \mathbb R^2$, and let $F(x) = \tilde P(x)^{-1} x$. Let $\nu, \xi$ be real with $\nu\xi \neq 0$ and $1 + \nu\xi \neq 0$, and $x = \xi(1,1)^T$. Then $F$ is differentiable at $x$ with Jacobian matrix (entry $(i,k)$ equal to $\partial F_i / \partial x_k$)
--   $$F'(x) = \tilde P(x)^{-1} + \frac{12\nu\xi}{(1+\nu\xi)^3}\begin{bmatrix} 2 & -1 \\ -4 & 2\end{bmatrix},$$
--   and this matrix is **not symmetric**.
--
--   Since the Jacobian of a gradient field is a Hessian, hence symmetric, this is the obstruction that rules out (3.8) for the example.
--
--   **Formalization Note** The paper writes the second term of $F'(x)$ as $\frac{12\nu\xi}{(1+\nu\xi)^3}\left[\begin{smallmatrix} 2 & -1 \\ -4 & 2\end{smallmatrix}\right]$, computed through a Kronecker formula for $\operatorname{vec}\tilde P'_x(h)$ that omits the minus sign forced by (3.9); with the sign restored, this matrix is the representation of $h \mapsto -\tilde P(x)^{-1}\tilde P'_x(h)\tilde P(x)^{-1}x$, so $F'(x) = \tilde P(x)^{-1}$ plus it, as stated. This was checked numerically by central differences. The non-symmetry conclusion is the paper's. The derivative is the linear map $h \mapsto F'(x) h$.
-- source:
--   Benner, Damm, Lyapunov Equations, Energy Functionals, and Model Order Reduction of Bilinear and Stochastic Systems, SIAM J. Control Optim. 49(2) (2011), p. 698, Example 3.3 (display ending "which is not symmetric")

import Mathlib
import Definitions.Def_BilinearGramian_Integrability_LinGramian
import Definitions.Def_BilinearGramian_Integrability_Example33

open Matrix

namespace BilinearGramian.Integrability

/-- Example 3.3, p. 698 (Benner–Damm 2011): let `P̃(x)` solve (3.9) for the example data at
every `x`, and `F(x) = P̃(x)⁻¹ x`. At `x = ξ (1, 1)ᵀ` with `1 + νξ ≠ 0`, the Jacobian
matrix of `F` (entry `(i, k)` is `∂F_i/∂x_k`) is
`P̃(x)⁻¹ + 12νξ/(1 + νξ)³ [2 -1; -4 2]`, and for `νξ ≠ 0` it is not symmetric. -/
theorem jacobian_not_symm (ν ξ : ℝ) (hνξ0 : ν * ξ ≠ 0) (hνξ : 1 + ν * ξ ≠ 0)
    (Pt : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ)
    (hPt : ∀ x, IsLinGramian exA (fun _ : Fin 1 => exN ν) exB x (Pt x)) :
    HasFDerivAt (fun y => (Pt y)⁻¹ *ᵥ y)
        (Matrix.toLin' ((Pt (ξ • ![1, 1]))⁻¹ +
          (12 * ν * ξ / (1 + ν * ξ) ^ 3) • !![2, -1; -4, 2])).toContinuousLinearMap
        (ξ • ![1, 1]) ∧
      ¬ ((Pt (ξ • ![1, 1]))⁻¹ + (12 * ν * ξ / (1 + ν * ξ) ^ 3) • !![2, -1; -4, 2]).IsSymm := by sorry

end BilinearGramian.Integrability
