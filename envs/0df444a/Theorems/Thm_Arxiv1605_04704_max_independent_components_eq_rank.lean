-- Prove2me | Theorems.Thm_Arxiv1605_04704_max_independent_components_eq_rank
-- name    : Arxiv1605_04704.max_independent_components_eq_rank
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T20:29:37.862444+00:00
-- url     : https://prove2.me/theorems/aa1e0cd0-5366-4d04-abf9-2d955c81f064
-- title:
--   Section 5, before case a: the maximum number of independent parallel components equals rank H_cov
-- statement:
--   Let $M_{\exp}$ be a real $4\times4$ matrix and $H(M_{\exp})=U\operatorname{diag}(\lambda_{\exp,0},\dots,\lambda_{\exp,3})U^\dagger$ with $U$ unitary and $\lambda_{\exp,0}\ge\dots\ge\lambda_{\exp,3}$, $\lambda_{\exp,0}>0$. Let $H_{\mathrm{cov}}$, $M_{\mathrm{cov}}$, its normalized eigenvalues $\hat\lambda_i$, its indices of purity $P_i$, its $m_{00}$ and its components $M_{Ui},M_2,M_3,M_{\Delta0}$ be those of the covariance filtering (eq. 23), and let $r=\operatorname{rank}H_{\mathrm{cov}}$. The maximum number $n$ of pure parallel components with positive weights and linearly independent covariance vectors, $H(M_{\mathrm{cov}})=\sum_{i<n}p_i\,m_{00}\,w_i\otimes w_i^\dagger$ as in eq. (6), is
--
--   $$\max n=r=\operatorname{rank}H_{\mathrm{cov}}.$$
--
--   In particular, when a number $q>r$ of components is hypothesized, $M_{\mathrm{cov}}$ admits no decomposition into $q$ such components.
--
--   **Formalization Note** "Independent parallel components" is read, following eq. (6), as pure components with linearly independent unit covariance vectors in $\operatorname{Range}H$ and positive weights summing to one.
--
--   **Formalization Note** The paper asks for $\lambda_{\mathrm{cov},0}=\lambda_0$ (the largest eigenvalue is not replaced), otherwise the measurement is rejected. The statement assumes $\lambda_{\exp,0}>0$, which also excludes $H_{\mathrm{cov}}=0$, where the normalization $\hat\lambda_i=\lambda_{\mathrm{cov},i}/\operatorname{tr}H_{\mathrm{cov}}$ is undefined.
-- source:
--   J. J. Gil, On optimal filtering of measured Mueller matrices, arXiv:1605.04704v3 (2016), claim c016; Section 5, paragraph before the case list a-d, right column of PDF p. 4

import Mathlib
import Definitions.Def_Arxiv1605_04704_Basic

open Matrix
open scoped ComplexOrder

namespace Arxiv1605_04704

theorem max_independent_components_eq_rank (Mexp : Matrix (Fin 4) (Fin 4) ℝ) (U : Matrix.unitaryGroup (Fin 4) ℂ) (lam : Fin 4 → ℝ)
    (hdat : IsCovFilterData Mexp U lam) (hlam0 : 0 < lam 0) :
    IsGreatest {n : ℕ | ∃ (p : Fin n → ℝ) (w : Fin n → Fin 4 → ℂ),
        IsPureDecomp (covMueller U lam) n p w ∧ ∀ i, 0 < p i} (covH U lam).rank := by sorry

end Arxiv1605_04704
