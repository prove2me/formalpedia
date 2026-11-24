-- Prove2me | Theorems.Thm_Arxiv1605_04704_case_b2_rank_three
-- name    : Arxiv1605_04704.case_b2_rank_three
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T21:27:41.34205+00:00
-- url     : https://prove2.me/theorems/ec640e9e-5141-4d65-8f3e-18a9332df3f5
-- title:
--   Section 5, case b.2: for r = 3 the filtered matrix is M_cov
-- statement:
--   Let $M_{\exp}$ be a real $4\times4$ matrix and $H(M_{\exp})=U\operatorname{diag}(\lambda_{\exp,0},\dots,\lambda_{\exp,3})U^\dagger$ with $U$ unitary and $\lambda_{\exp,0}\ge\dots\ge\lambda_{\exp,3}$, $\lambda_{\exp,0}>0$. Let $H_{\mathrm{cov}}$, $M_{\mathrm{cov}}$, its normalized eigenvalues $\hat\lambda_i$, its indices of purity $P_i$, its $m_{00}$ and its components $M_{Ui},M_2,M_3,M_{\Delta0}$ be those of the covariance filtering (eq. 23), and let $r=\operatorname{rank}H_{\mathrm{cov}}$. If $r=3$, the filtered matrix of eq. (24) is $M_{\mathrm{cov}}$ itself:
--
--   $$\frac{M_{\mathrm{cov}}-(1-P_3)M_{\Delta0}}{P_3}=M_{\mathrm{cov}}.$$
--
--   **Formalization Note** The paper's case b.2 ("if $r=3$, then simply $M_f=M_{\mathrm{cov}}$") is a prescription. It is formalized as the statement that the formula of case b.1 returns $M_{\mathrm{cov}}$ when $r=3$, so the two cases are consistent.
--
--   **Formalization Note** The paper asks for $\lambda_{\mathrm{cov},0}=\lambda_0$ (the largest eigenvalue is not replaced), otherwise the measurement is rejected. The statement assumes $\lambda_{\exp,0}>0$, which also excludes $H_{\mathrm{cov}}=0$, where the normalization $\hat\lambda_i=\lambda_{\mathrm{cov},i}/\operatorname{tr}H_{\mathrm{cov}}$ is undefined.
-- source:
--   J. J. Gil, On optimal filtering of measured Mueller matrices, arXiv:1605.04704v3 (2016), claim c009; Section 5, case b.2 (q = 3, r = 3), PDF p. 5

import Mathlib
import Definitions.Def_Arxiv1605_04704_Basic

open Matrix
open scoped ComplexOrder

namespace Arxiv1605_04704

theorem case_b2_rank_three (Mexp : Matrix (Fin 4) (Fin 4) ℝ) (U : Matrix.unitaryGroup (Fin 4) ℂ) (lam : Fin 4 → ℝ)
    (hdat : IsCovFilterData Mexp U lam) (hlam0 : 0 < lam 0)
    (hr : (covH U lam).rank = 3) :
    filt3 U lam = covMueller U lam := by sorry

end Arxiv1605_04704
