-- Prove2me | Theorems.Thm_DavidonVM_Termination_hereditary
-- name    : DavidonVM.Termination.hereditary
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:43:49.064613+00:00
-- url     : https://prove2.me/theorems/4de50d1e-af16-4583-8fac-16d75275edc7
-- title:
--   Appendix, after (8) — along the run every past step S_j satisfies H_k G S_j = S_j
-- statement:
--   Let $G$ be a symmetric real $n\times n$ matrix and $\xi\in\mathbb R^n$. Let $(x_k)$, $(H_k)$ be a run of Davidon's method on the quadratic with gradient $\nabla(x)=G(x-\xi)$ and coefficients $a_k=(M_k-N_k)^{-1}$, where $N_k=\nabla_{k+1}^{\mathsf T}H_k\nabla_{k+1}$ and $M_k=\nabla_{k+1}^{\mathsf T}H_k\nabla_k$, starting from a symmetric $H_0$. Fix $k\ge 0$ and suppose $M_i\ne N_i$ for every $i<k$. Then every step taken so far, $S_j=x_{j+1}-x_j$ with $j<k$, satisfies
--   $$
--   H_k\,G\,S_j=S_j .
--   $$
--
--   This is the sentence "so that $S$ becomes another such eigenvector" of p. 17 read along the run: each step becomes an eigenvector of $H G$ with eigenvalue one when it is taken (display (8)) and stays one afterwards (display (7)). It is the property from which the termination claim follows.
--
--   **Formalization Note** "For which $\Delta=0$" is read through footnote 2 as $M_i\ne N_i$ for the steps used. Only $H_0$ is assumed symmetric; symmetry of later $H_k$ is a consequence, not a hypothesis. $G$ need only be symmetric here. Indices are 0-based.
-- source:
--   Davidon, Variable Metric Method for Minimization, SIAM J. Optim. 1(1) (1991), p. 17, Appendix, sentence after (8)

import Mathlib
import Definitions.Def_DavidonVM_Termination_Method

open Matrix

namespace DavidonVM.Termination

/-- Appendix, sentence after (8), p. 17, read along a run: on the quadratic with constant
symmetric Hessian `G`, if `H₀` is symmetric and the first `k` updates have `M_i ≠ N_i`,
then every step `S_j = x_{j+1} − x_j`, `j < k`, satisfies `H_k G S_j = S_j`. -/
theorem hereditary {n : ℕ} (G : Mat n) (hG : G.IsSymm) (ξ : Vec n) (x : ℕ → Vec n)
    (H : ℕ → Mat n) (hH0 : (H 0).IsSymm) (hrun : IsQuadRun G ξ x H) (k : ℕ)
    (hMN : ∀ i < k, Mval (grad G ξ) x H i ≠ Nval (grad G ξ) x H i) :
    ∀ j < k, H k *ᵥ (G *ᵥ (x (j + 1) - x j)) = x (j + 1) - x j := by sorry

end DavidonVM.Termination
