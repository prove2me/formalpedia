-- Prove2me | Theorems.Thm_Arxiv1605_04704_case_c1_not_proportional
-- name    : Arxiv1605_04704.case_c1_not_proportional
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T21:53:46.110577+00:00
-- url     : https://prove2.me/theorems/393ca26e-fd98-4daf-a791-700ed5eebc2d
-- title:
--   Section 5, case c.1, after eq. (29): the filtered weights are not proportional to the spectral weights
-- statement:
--   Let $M_{\exp}$ be a real $4\times4$ matrix and $H(M_{\exp})=U\operatorname{diag}(\lambda_{\exp,0},\dots,\lambda_{\exp,3})U^\dagger$ with $U$ unitary and $\lambda_{\exp,0}\ge\dots\ge\lambda_{\exp,3}$, $\lambda_{\exp,0}>0$. Let $H_{\mathrm{cov}}$, $M_{\mathrm{cov}}$, its normalized eigenvalues $\hat\lambda_i$, its indices of purity $P_i$, its $m_{00}$ and its components $M_{Ui},M_2,M_3,M_{\Delta0}$ be those of the covariance filtering (eq. 23), and let $r=\operatorname{rank}H_{\mathrm{cov}}$. Assume $r>2$ and $\hat\lambda_0\ne\hat\lambda_1$. Then the weights $p_0,p_1$ of $M_{U0},M_{U1}$ in $M_f$ (eq. 29) are not proportional to $\hat\lambda_0,\hat\lambda_1$: there is no $k$ with $p_0=k\hat\lambda_0$ and $p_1=k\hat\lambda_1$.
--
--   **Formalization Note** The paper states non-proportionality without exception. If $\hat\lambda_0=\hat\lambda_1$ the weights are $1/2,1/2$ and are proportional, so the statement assumes $\hat\lambda_0\ne\hat\lambda_1$.
--
--   **Formalization Note** The paper asks for $\lambda_{\mathrm{cov},0}=\lambda_0$ (the largest eigenvalue is not replaced), otherwise the measurement is rejected. The statement assumes $\lambda_{\exp,0}>0$, which also excludes $H_{\mathrm{cov}}=0$, where the normalization $\hat\lambda_i=\lambda_{\mathrm{cov},i}/\operatorname{tr}H_{\mathrm{cov}}$ is undefined.
-- source:
--   J. J. Gil, On optimal filtering of measured Mueller matrices, arXiv:1605.04704v3 (2016), claim c012; Section 5, case c.1, paragraph after eq. (29), PDF p. 5

import Mathlib
import Definitions.Def_Arxiv1605_04704_Basic

open Matrix
open scoped ComplexOrder

namespace Arxiv1605_04704

theorem case_c1_not_proportional (Mexp : Matrix (Fin 4) (Fin 4) ℝ) (U : Matrix.unitaryGroup (Fin 4) ℂ) (lam : Fin 4 → ℝ)
    (hdat : IsCovFilterData Mexp U lam) (hlam0 : 0 < lam 0)
    (hr : 2 < (covH U lam).rank) :
    let l := covLhat lam
    l 0 ≠ l 1 →
      ∀ k : ℝ, ¬ ((l 0 - l 2) / (l 0 + l 1 - 2 * l 2) = k * l 0 ∧
        (l 1 - l 2) / (l 0 + l 1 - 2 * l 2) = k * l 1) := by sorry

end Arxiv1605_04704
