-- Prove2me | Theorems.Thm_BoydADMM_Nonconvex_factor_model_partial_minimization
-- name    : BoydADMM.Nonconvex.factor_model_partial_minimization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T02:19:45.820368+00:00
-- url     : https://prove2.me/theorems/5f103d4c-cf46-4645-8018-8f55c73710b6
-- title:
--   §9.1.2 — eliminate the nonnegative diagonal in the factor-model loss
-- statement:
--   Let $n\ge1$ and let $\Sigma,X\in\mathbb R^{n\times n}$ be symmetric. Define $f_\Sigma(X)=\inf_{d\ge0}\frac12\|X+\operatorname{diag}(d)-\Sigma\|_F^2$. Then
--
--   $$f_\Sigma(X)=\frac12\sum_{i\ne j}(X_{ij}-\Sigma_{ij})^2+\frac12\sum_{i=1}^n(X_{ii}-\Sigma_{ii})_+^2,$$
--
--   and the infimum is attained by $d_i=(\Sigma_{ii}-X_{ii})_+$, which is componentwise nonnegative.
--
--   This identifies the reduced convex loss that appears in the factor-model ADMM X-update.
--
--   **Formalization Note** The sum over $i\ne j$ includes both ordered entries $(i,j)$ and $(j,i)$, as in the Frobenius norm. The book treats $n$ as a positive matrix dimension; Lean states $n\ge1$ explicitly.
-- source:
--   Boyd, Parikh, Chu, Peleato, Eckstein, Distributed Optimization and Statistical Learning via the Alternating Direction Method of Multipliers, Found. Trends Mach. Learn. 3(1) (2011), p. 75, §9.1.2, display beginning f(X) = inf

import Mathlib
import Definitions.Def_BoydADMM_Nonconvex_FactorModel

namespace BoydADMM.Nonconvex

/-- §9.1.2, p. 75: eliminating the nonnegative diagonal gives the stated
componentwise loss, attained at `d_i = (Σ_ii - X_ii)_+`. -/
theorem factor_model_partial_minimization {n : ℕ} (Sigma X : SqMat n)
    (hn : 0 < n) (hSigma : IsSymmetric Sigma) (hX : IsSymmetric X) :
    factorLoss Sigma X = factorLossExplicit Sigma X ∧
    (∀ i, 0 ≤ optimalDiag Sigma X i) ∧
    factorLossWithDiag Sigma X (optimalDiag Sigma X) = factorLoss Sigma X := by sorry

end BoydADMM.Nonconvex
