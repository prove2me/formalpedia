-- Prove2me | Theorems.Thm_CaiCandesShen_Convergence_shrink_well_defined
-- name    : CaiCandesShen.Convergence.shrink_well_defined
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:13:50.983343+00:00
-- url     : https://prove2.me/theorems/f3118dee-dca5-468b-b69e-655f7be83e1b
-- title:
--   §2.1 — the singular value shrinkage operator $\mathcal D_\tau$ is well defined
-- statement:
--   Let $\tau\ge0$ and $Y\in\mathbb R^{n_1\times n_2}$. Even though the reduced SVD $Y=U\Sigma V^*$ of (2.1) need not be unique, the matrix
--   $$\mathcal D_\tau(Y)=U\operatorname{diag}(\{(\sigma_i-\tau)_+\})V^*$$
--   does not depend on the choice: there is exactly one matrix $X$ such that $X=U\operatorname{diag}((\sigma_i-\tau)_+)V^*$ for some reduced SVD $(U,\sigma,V)$ of $Y$.
--
--   The statement contains both existence of a reduced SVD for every real matrix and independence of the output from the choice of SVD, so that $\mathcal D_\tau$ is a genuine function.
-- source:
--   Cai, Candès, Shen, A Singular Value Thresholding Algorithm for Matrix Completion, SIAM J. Optim. 20 (2010), p. 1960, §2.1, first paragraph

import Mathlib
import Definitions.Def_CaiCandesShen_Convergence_Shrink

namespace CaiCandesShen.Convergence

/-- §2.1, p. 1960: even though the SVD may not be unique, the singular value shrinkage operator
`D_τ` of (2.2) is well defined: every real matrix `Y` has exactly one `X` with `X = D_τ(Y)`. -/
theorem shrink_well_defined {n₁ n₂ : ℕ} (τ : ℝ) (hτ : 0 ≤ τ) (Y : Mat n₁ n₂) :
    ∃! X : Mat n₁ n₂, IsShrink τ Y X := by sorry

end CaiCandesShen.Convergence
