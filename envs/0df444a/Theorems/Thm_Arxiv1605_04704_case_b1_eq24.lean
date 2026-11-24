-- Prove2me | Theorems.Thm_Arxiv1605_04704_case_b1_eq24
-- name    : Arxiv1605_04704.case_b1_eq24
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T21:01:19.765883+00:00
-- url     : https://prove2.me/theorems/bb9233fe-c5a1-41eb-8281-8d4b4d69d33f
-- title:
--   Section 5, case b.1, eq. (24): subtracting the ideal depolarizer
-- statement:
--   Let $M_{\exp}$ be a real $4\times4$ matrix and $H(M_{\exp})=U\operatorname{diag}(\lambda_{\exp,0},\dots,\lambda_{\exp,3})U^\dagger$ with $U$ unitary and $\lambda_{\exp,0}\ge\dots\ge\lambda_{\exp,3}$, $\lambda_{\exp,0}>0$. Let $H_{\mathrm{cov}}$, $M_{\mathrm{cov}}$, its normalized eigenvalues $\hat\lambda_i$, its indices of purity $P_i$, its $m_{00}$ and its components $M_{Ui},M_2,M_3,M_{\Delta0}$ be those of the covariance filtering (eq. 23), and let $r=\operatorname{rank}H_{\mathrm{cov}}$. Assume $r=4$ and $P_3>0$. Then the filtered matrix of eq. (24) satisfies
--
--   $$M_f=\frac{M_{\mathrm{cov}}-(1-P_3)M_{\Delta0}}{P_3}=\frac{P_1M_{U0}+(P_2-P_1)M_2+(P_3-P_2)M_3}{P_3}.$$
--
--   **Formalization Note** The hypothesis $P_3>0$ is not written in the paper. It is needed for the division: with $r=4$, $P_3=0$ exactly when all four $\hat\lambda_i$ equal $1/4$. The sentence that a significant coefficient $1-P_3\gg\delta$ implies four non-negligible components is not quantified and is not formalized.
--
--   **Formalization Note** The paper asks for $\lambda_{\mathrm{cov},0}=\lambda_0$ (the largest eigenvalue is not replaced), otherwise the measurement is rejected. The statement assumes $\lambda_{\exp,0}>0$, which also excludes $H_{\mathrm{cov}}=0$, where the normalization $\hat\lambda_i=\lambda_{\mathrm{cov},i}/\operatorname{tr}H_{\mathrm{cov}}$ is undefined.
-- source:
--   J. J. Gil, On optimal filtering of measured Mueller matrices, arXiv:1605.04704v3 (2016), claim c018; Section 5, case b.1 (q = 3, r = 4), eq. (24), right column of PDF p. 4

import Mathlib
import Definitions.Def_Arxiv1605_04704_Basic

open Matrix
open scoped ComplexOrder

namespace Arxiv1605_04704

theorem case_b1_eq24 (Mexp : Matrix (Fin 4) (Fin 4) ℝ) (U : Matrix.unitaryGroup (Fin 4) ℂ) (lam : Fin 4 → ℝ)
    (hdat : IsCovFilterData Mexp U lam) (hlam0 : 0 < lam 0)
    (hr : (covH U lam).rank = 4) (hP3 : 0 < ipp3 (covLhat lam)) :
    filt3 U lam = (1 / ipp3 (covLhat lam)) •
      (ipp1 (covLhat lam) • specComp U (covMueller U lam 0 0) 0 +
        (ipp2 (covLhat lam) - ipp1 (covLhat lam)) • depol2 U (covMueller U lam 0 0) +
        (ipp3 (covLhat lam) - ipp2 (covLhat lam)) • depol3 U (covMueller U lam 0 0)) := by sorry

end Arxiv1605_04704
