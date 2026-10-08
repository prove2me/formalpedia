-- Prove2me | Theorems.Thm_DavidonVM_Termination_quadratic_termination
-- name    : DavidonVM.Termination.quadratic_termination
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:42:40.243995+00:00
-- url     : https://prove2.me/theorems/993a4d76-5679-4a01-81d5-c4ef6743865c
-- title:
--   Appendix, after (8) — after n steps with Δ = 0, H equals G⁻¹ and the next step reaches the exact minimum
-- statement:
--   Let $G$ be a symmetric positive definite real $n\times n$ matrix and $\xi\in\mathbb R^n$, so that $f(x)=\tfrac12(x-\xi)^{\mathsf T}G(x-\xi)+c$ has its unique minimum at $\xi$ and gradient $\nabla(x)=G(x-\xi)$. Run Davidon's method from any point $x_0$ and any symmetric matrix $H_0$:
--   $$
--   x_{k+1}=x_k-H_k\nabla_k,\qquad H_{k+1}=H_k+a_k\,(H_k\nabla_{k+1})(H_k\nabla_{k+1})^{\mathsf T},\qquad a_k=(M_k-N_k)^{-1},
--   $$
--   where $\nabla_k=\nabla(x_k)$, $N_k=\nabla_{k+1}^{\mathsf T}H_k\nabla_{k+1}$ and $M_k=\nabla_{k+1}^{\mathsf T}H_k\nabla_k$. If $M_k\ne N_k$ for every $k<n$, then
--   $$
--   H_n=G^{-1}\qquad\text{and}\qquad x_{n+1}=\xi .
--   $$
--
--   This is the paper's termination claim, p. 17: "After no more than $N$ steps (for which $\Delta=0$), $H$ will equal $G^{-1}$ and the following step will be to the exact minimum." It is the abstract's statement that for a quadratic no more than $N$ iterations are required, where $N$ is the number of variables.
--
--   **Formalization Note** The paper's $N$ (number of variables) is $n$. "Steps for which $\Delta=0$" is read through footnote 2: on a quadratic the coefficient $a_k=(M_k-N_k)^{-1}$ makes $\Delta=0$, and we require that this coefficient is defined, $M_k\ne N_k$, for the first $n$ steps. No linear independence of the steps and no positive definiteness of $H_0$ is assumed; only symmetry of $H_0$ (p. 4). $G^{-1}$ is the matrix inverse. "No more than $N$ steps" is stated at exactly $n$ steps; the stopping rule of p. 17 is not modelled, so the run continues through step $n+1$.
-- source:
--   Davidon, Variable Metric Method for Minimization, SIAM J. Optim. 1(1) (1991), p. 17, Appendix, sentence after (8); abstract p. 1

import Mathlib
import Definitions.Def_DavidonVM_Termination_Method

open Matrix

namespace DavidonVM.Termination

/-- Appendix, sentence after (8), p. 17: on the quadratic with constant positive definite
Hessian `G` and minimum point `ξ`, starting from a symmetric `H₀`, if the first `n` steps
have `M_k ≠ N_k` (so that footnote 2's `a_k = (M_k − N_k)⁻¹` is defined), then
`H_n = G⁻¹` and the following step lands at the minimum: `x_{n+1} = ξ`. -/
theorem quadratic_termination {n : ℕ} (G : Mat n) (hG : G.PosDef) (ξ : Vec n)
    (x : ℕ → Vec n) (H : ℕ → Mat n) (hH0 : (H 0).IsSymm) (hrun : IsQuadRun G ξ x H)
    (hMN : ∀ k < n, Mval (grad G ξ) x H k ≠ Nval (grad G ξ) x H k) :
    H n = G⁻¹ ∧ x (n + 1) = ξ := by sorry

end DavidonVM.Termination
