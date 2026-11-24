-- Prove2me | Theorems.Thm_Arxiv1605_04704_case_d_pure_weight
-- name    : Arxiv1605_04704.case_d_pure_weight
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T20:51:46.339928+00:00
-- url     : https://prove2.me/theorems/3742705d-7f0c-43b2-9992-4b59efc98534
-- title:
--   Section 5, case d (q = 1): after subtracting the 4D, 3D and 2D noise the weight of M_U0 is P1
-- statement:
--   Let $M_{\exp}$ be a real $4\times4$ matrix and $H(M_{\exp})=U\operatorname{diag}(\lambda_{\exp,0},\dots,\lambda_{\exp,3})U^\dagger$ with $U$ unitary and $\lambda_{\exp,0}\ge\dots\ge\lambda_{\exp,3}$, $\lambda_{\exp,0}>0$. Let $H_{\mathrm{cov}}$, $M_{\mathrm{cov}}$, its normalized eigenvalues $\hat\lambda_i$, its indices of purity $P_i$, its $m_{00}$ and its components $M_{Ui},M_2,M_3,M_{\Delta0}$ be those of the covariance filtering (eq. 23), and let $r=\operatorname{rank}H_{\mathrm{cov}}$. After the 4D, 3D and 2D noise contributions of the characteristic decomposition are subtracted, what remains is the characteristic component with weight $P_1$:
--
--   $$M_{\mathrm{cov}}-(1-P_3)M_{\Delta0}-(P_3-P_2)M_3-(P_2-P_1)M_2=P_1\,M_{U0}.$$
--
--   **Formalization Note** The weight is the coefficient before any renormalization, which is how the paper's "relative weight ... is given by $P_1$" is read.
--
--   **Formalization Note** The paper asks for $\lambda_{\mathrm{cov},0}=\lambda_0$ (the largest eigenvalue is not replaced), otherwise the measurement is rejected. The statement assumes $\lambda_{\exp,0}>0$, which also excludes $H_{\mathrm{cov}}=0$, where the normalization $\hat\lambda_i=\lambda_{\mathrm{cov},i}/\operatorname{tr}H_{\mathrm{cov}}$ is undefined.
-- source:
--   J. J. Gil, On optimal filtering of measured Mueller matrices, arXiv:1605.04704v3 (2016), claim c014; Section 5, case d, with eq. (15), PDF p. 5

import Mathlib
import Definitions.Def_Arxiv1605_04704_Basic

open Matrix
open scoped ComplexOrder

namespace Arxiv1605_04704

theorem case_d_pure_weight (Mexp : Matrix (Fin 4) (Fin 4) ℝ) (U : Matrix.unitaryGroup (Fin 4) ℂ) (lam : Fin 4 → ℝ)
    (hdat : IsCovFilterData Mexp U lam) (hlam0 : 0 < lam 0) :
    covMueller U lam - (1 - ipp3 (covLhat lam)) • idealDepol (covMueller U lam 0 0) -
        (ipp3 (covLhat lam) - ipp2 (covLhat lam)) • depol3 U (covMueller U lam 0 0) -
        (ipp2 (covLhat lam) - ipp1 (covLhat lam)) • depol2 U (covMueller U lam 0 0) =
      ipp1 (covLhat lam) • specComp U (covMueller U lam 0 0) 0 := by sorry

end Arxiv1605_04704
