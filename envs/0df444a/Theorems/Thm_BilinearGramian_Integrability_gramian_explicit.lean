-- Prove2me | Theorems.Thm_BilinearGramian_Integrability_gramian_explicit
-- name    : BilinearGramian.Integrability.gramian_explicit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:38:58.583983+00:00
-- url     : https://prove2.me/theorems/d4330110-40ed-416f-97da-dcb80ccd5bd9
-- title:
--   Example 3.3, p. 698 — P̃(x) = (1 + νξ)²[1/2 1/3; 1/3 1/4] and its inverse at x = ξ(1, 1)ᵀ
-- statement:
--   Let $A, N = N(\nu), b$ be the data of Example 3.3, let $\xi \in \mathbb R$ with $1 + \nu\xi \neq 0$, and let $x = \xi (1,1)^T$. Then $Nx + b = (1+\nu\xi)(1,1)^T$, and any matrix $\tilde P(x)$ solving (3.9) at $x$,
--   $$A \tilde P(x) + \tilde P(x) A^T = -(Nx+b)(Nx+b)^T = -(1+\nu\xi)^2 \begin{bmatrix} 1 & 1 \\ 1 & 1\end{bmatrix},$$
--   equals
--   $$\tilde P(x) = (1+\nu\xi)^2 \begin{bmatrix} 1/2 & 1/3 \\ 1/3 & 1/4 \end{bmatrix}, \qquad \text{and}\qquad \tilde P(x)^{-1} = \frac{6}{(1+\nu\xi)^2}\begin{bmatrix} 3 & -4 \\ -4 & 6\end{bmatrix}.$$
--
--   This explicit Gramian is the input to the computation of the Jacobian of $F(x) = \tilde P(x)^{-1}x$ in Example 3.3.
--
--   **Formalization Note** The hypothesis $1 + \nu\xi \neq 0$ is implicit in the paper's inverse formula: at $1 + \nu\xi = 0$ the Gramian is the zero matrix and has no inverse.
-- source:
--   Benner, Damm, Lyapunov Equations, Energy Functionals, and Model Order Reduction of Bilinear and Stochastic Systems, SIAM J. Control Optim. 49(2) (2011), p. 698, Example 3.3

import Mathlib
import Definitions.Def_BilinearGramian_Integrability_LinGramian
import Definitions.Def_BilinearGramian_Integrability_Example33

open Matrix

namespace BilinearGramian.Integrability

/-- Example 3.3, p. 698 (Benner–Damm 2011): at `x = ξ (1, 1)ᵀ` the solution of (3.9) for the
example data is `P̃(x) = (1 + νξ)² [1/2 1/3; 1/3 1/4]`, with inverse
`P̃(x)⁻¹ = 6/(1 + νξ)² [3 -4; -4 6]`. -/
theorem gramian_explicit (ν ξ : ℝ) (hνξ : 1 + ν * ξ ≠ 0) (P : Matrix (Fin 2) (Fin 2) ℝ)
    (hP : IsLinGramian exA (fun _ : Fin 1 => exN ν) exB (ξ • ![1, 1]) P) :
    P = (1 + ν * ξ) ^ 2 • !![1 / 2, 1 / 3; 1 / 3, 1 / 4] ∧
      P⁻¹ = (6 / (1 + ν * ξ) ^ 2) • !![3, -4; -4, 6] := by sorry

end BilinearGramian.Integrability
