-- Prove2me | Theorems.Thm_Arxiv1605_04704_case_b1_not_proportional
-- name    : Arxiv1605_04704.case_b1_not_proportional
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T21:19:22.365735+00:00
-- url     : https://prove2.me/theorems/d1e1ddd9-d42c-41d2-a7c0-de8baa37ef0a
-- title:
--   Section 5, case b.1, after eq. (26): the filtered weights are not proportional to the spectral weights
-- statement:
--   Let $M_{\exp}$ be a real $4\times4$ matrix and $H(M_{\exp})=U\operatorname{diag}(\lambda_{\exp,0},\dots,\lambda_{\exp,3})U^\dagger$ with $U$ unitary and $\lambda_{\exp,0}\ge\dots\ge\lambda_{\exp,3}$, $\lambda_{\exp,0}>0$. Let $H_{\mathrm{cov}}$, $M_{\mathrm{cov}}$, its normalized eigenvalues $\hat\lambda_i$, its indices of purity $P_i$, its $m_{00}$ and its components $M_{Ui},M_2,M_3,M_{\Delta0}$ be those of the covariance filtering (eq. 23), and let $r=\operatorname{rank}H_{\mathrm{cov}}$. Assume $r=4$, and that $\hat\lambda_0,\hat\lambda_1,\hat\lambda_2$ are not all equal. Then the weights $p_i=(\hat\lambda_i-\hat\lambda_3)/(1-4\hat\lambda_3)$ of $M_{U0},M_{U1},M_{U2}$ in $M_f$ (eq. 26) are not proportional to $\hat\lambda_0,\hat\lambda_1,\hat\lambda_2$: there is no $k$ with $p_i=k\hat\lambda_i$ for $i=0,1,2$. In particular they differ from the weights $\hat\lambda_i/(1-\hat\lambda_3)$ obtained by dropping the fourth spectral component and renormalizing.
--
--   **Formalization Note** The paper states non-proportionality without exception. If $\hat\lambda_0=\hat\lambda_1=\hat\lambda_2$, then $p_i=1/3=\hat\lambda_i/(1-\hat\lambda_3)$ and the weights are proportional. The statement therefore carries the hypothesis that the three largest eigenvalues are not all equal, as in the paper's "may lead to an incorrect evaluation".
--
--   **Formalization Note** The paper asks for $\lambda_{\mathrm{cov},0}=\lambda_0$ (the largest eigenvalue is not replaced), otherwise the measurement is rejected. The statement assumes $\lambda_{\exp,0}>0$, which also excludes $H_{\mathrm{cov}}=0$, where the normalization $\hat\lambda_i=\lambda_{\mathrm{cov},i}/\operatorname{tr}H_{\mathrm{cov}}$ is undefined.
-- source:
--   J. J. Gil, On optimal filtering of measured Mueller matrices, arXiv:1605.04704v3 (2016), claim c008; Section 5, case b.1, paragraph after eq. (26), PDF p. 5

import Mathlib
import Definitions.Def_Arxiv1605_04704_Basic

open Matrix
open scoped ComplexOrder

namespace Arxiv1605_04704

theorem case_b1_not_proportional (Mexp : Matrix (Fin 4) (Fin 4) ℝ) (U : Matrix.unitaryGroup (Fin 4) ℂ) (lam : Fin 4 → ℝ)
    (hdat : IsCovFilterData Mexp U lam) (hlam0 : 0 < lam 0)
    (hr : (covH U lam).rank = 4) :
    let l := covLhat lam
    ¬ (l 0 = l 1 ∧ l 1 = l 2) →
      ∀ k : ℝ, ¬ ((l 0 - l 3) / (1 - 4 * l 3) = k * l 0 ∧ (l 1 - l 3) / (1 - 4 * l 3) = k * l 1 ∧
        (l 2 - l 3) / (1 - 4 * l 3) = k * l 2) := by sorry

end Arxiv1605_04704
