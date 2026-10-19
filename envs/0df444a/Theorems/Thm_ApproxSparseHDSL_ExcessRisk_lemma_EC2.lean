-- Prove2me | Theorems.Thm_ApproxSparseHDSL_ExcessRisk_lemma_EC2
-- name    : ApproxSparseHDSL.ExcessRisk.lemma_EC2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:53:06.622058+00:00
-- url     : https://prove2.me/theorems/5589bbfb-b8da-4211-9c1d-3630033c0cd5
-- title:
--   Lemma EC.2, p. ec42 — the Lasso solution compared with β*_εA in the MCP objective
-- statement:
--   Fix a sample $Z_1^n$ and MCP parameters $a, \lambda > 0$. If $\hat\beta^{\ell_1}$ is an optimal solution of $\min_\beta \mathcal L_n(\beta, Z_1^n) + \lambda|\beta|$ (the Lasso (5), $|\cdot|$ the $\ell_1$ norm), then
--
--   $$
--   \mathcal L_{n,\lambda}(\hat\beta^{\ell_1}, Z_1^n) \le \mathcal L_{n,\lambda}(\beta^*_{\varepsilon_A}, Z_1^n) + \lambda|\beta^*_{\varepsilon_A}|.
--   $$
--
--   It lets the Lasso solution serve as a starting point for which the gap $\Gamma$ of Proposition 5 (i) is $\lambda|\beta^*_{\varepsilon_A}|$.
--
--   **Formalization Note** The comparison vector $\beta^*_{\varepsilon_A}$ enters only as a vector, so the statement is made for every $\beta^* \in \mathbb R^p$.
-- source:
--   Liu, Ye & Lee, High-dimensional learning under approximate sparsity with applications to nonsmooth estimation and regularized neural networks, arXiv:1903.00616v2, p. ec42, Lemma EC.2

import Mathlib
import Definitions.Def_ApproxSparseHDSL_ExcessRisk_Model

open MeasureTheory ProbabilityTheory

namespace ApproxSparseHDSL.ExcessRisk

/-- Lemma EC.2, p. ec42: for a fixed sample `z`, if `β̂^{ℓ₁}` minimizes the Lasso objective
`ℒₙ(β, z) + λ|β|`, then `ℒₙ,λ(β̂^{ℓ₁}, z) ≤ ℒₙ,λ(β, z) + λ|β|` for the comparison vector
`β = β*_εA` (stated for every vector `betaStar`). -/
theorem lemma_EC2 {E : Type} {p n : ℕ} (L : (Fin p → ℝ) → E → ℝ) (z : Fin n → E)
    (a lam : ℝ) (ha : 0 < a) (hlam : 0 < lam) (betaL1 betaStar : Fin p → ℝ)
    (hopt : ∀ β : Fin p → ℝ, lassoObj lam L z betaL1 ≤ lassoObj lam L z β) :
    regRisk a lam L z betaL1 ≤ regRisk a lam L z betaStar + lam * l1 betaStar := by sorry

end ApproxSparseHDSL.ExcessRisk
