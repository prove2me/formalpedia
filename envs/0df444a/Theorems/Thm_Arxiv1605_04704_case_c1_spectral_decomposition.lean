-- Prove2me | Theorems.Thm_Arxiv1605_04704_case_c1_spectral_decomposition
-- name    : Arxiv1605_04704.case_c1_spectral_decomposition
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T21:45:00.495052+00:00
-- url     : https://prove2.me/theorems/79dd93f3-82e1-4d83-b7b4-76f72d6b16c8
-- title:
--   Section 5, case c.1, eqs. (28)-(29): spectral decomposition of the filtered matrix for q = 2, r > 2
-- statement:
--   Let $M_{\exp}$ be a real $4\times4$ matrix and $H(M_{\exp})=U\operatorname{diag}(\lambda_{\exp,0},\dots,\lambda_{\exp,3})U^\dagger$ with $U$ unitary and $\lambda_{\exp,0}\ge\dots\ge\lambda_{\exp,3}$, $\lambda_{\exp,0}>0$. Let $H_{\mathrm{cov}}$, $M_{\mathrm{cov}}$, its normalized eigenvalues $\hat\lambda_i$, its indices of purity $P_i$, its $m_{00}$ and its components $M_{Ui},M_2,M_3,M_{\Delta0}$ be those of the covariance filtering (eq. 23), and let $r=\operatorname{rank}H_{\mathrm{cov}}$. Assume $r>2$ and $P_2>0$, and let $M_f=[M_{\mathrm{cov}}-(1-P_3)M_{\Delta0}-(P_3-P_2)M_3]/P_2$ (eq. 27). Put
--
--   $$p_0=\frac{\hat\lambda_0-\hat\lambda_2}{\hat\lambda_0+\hat\lambda_1-2\hat\lambda_2},\qquad p_1=\frac{\hat\lambda_1-\hat\lambda_2}{\hat\lambda_0+\hat\lambda_1-2\hat\lambda_2}.$$
--
--   Then
--
--   $$M_f=p_0M_{U0}+p_1M_{U1},\qquad p_0=\tfrac12\Big(1+\tfrac{P_1}{P_2}\Big),\quad p_1=\tfrac12\Big(1-\tfrac{P_1}{P_2}\Big).$$
--
--   The sum is convex, and it is the spectral decomposition of $M_f$. That is, $M_f$ has the same $m_{00}$ as $M_{\mathrm{cov}}$, and $H(M_f)=m_{00}U\operatorname{diag}(p_0,p_1,0,0)U^\dagger$ with $p_0\ge p_1\ge0$.
--
--   This is eqs. (28)-(29).
--
--   **Formalization Note** The hypothesis $P_2>0$ is not written in the paper. "Spectral decomposition of $M_f$" is stated as: $(U,(p_0,p_1,0,0))$ is ordered spectral data for $M_f$.
--
--   **Formalization Note** The paper asks for $\lambda_{\mathrm{cov},0}=\lambda_0$ (the largest eigenvalue is not replaced), otherwise the measurement is rejected. The statement assumes $\lambda_{\exp,0}>0$, which also excludes $H_{\mathrm{cov}}=0$, where the normalization $\hat\lambda_i=\lambda_{\mathrm{cov},i}/\operatorname{tr}H_{\mathrm{cov}}$ is undefined.
-- source:
--   J. J. Gil, On optimal filtering of measured Mueller matrices, arXiv:1605.04704v3 (2016), claim c011; Section 5, case c.1 (q = 2, r > 2), eqs. (27)-(29), PDF p. 5

import Mathlib
import Definitions.Def_Arxiv1605_04704_Basic

open Matrix
open scoped ComplexOrder

namespace Arxiv1605_04704

theorem case_c1_spectral_decomposition (Mexp : Matrix (Fin 4) (Fin 4) ℝ) (U : Matrix.unitaryGroup (Fin 4) ℂ) (lam : Fin 4 → ℝ)
    (hdat : IsCovFilterData Mexp U lam) (hlam0 : 0 < lam 0)
    (hr : 2 < (covH U lam).rank) (hP2 : 0 < ipp2 (covLhat lam)) :
    let l := covLhat lam
    let c := covMueller U lam 0 0
    let p : Fin 4 → ℝ := ![(l 0 - l 2) / (l 0 + l 1 - 2 * l 2), (l 1 - l 2) / (l 0 + l 1 - 2 * l 2),
      0, 0]
    filt2 U lam = p 0 • specComp U c 0 + p 1 • specComp U c 1 ∧
    p 0 = (1 / 2) * (1 + ipp1 l / ipp2 l) ∧ p 1 = (1 / 2) * (1 - ipp1 l / ipp2 l) ∧
    (∀ i, 0 ≤ p i) ∧ p 0 + p 1 = 1 ∧
    filt2 U lam 0 0 = c ∧ IsSpectralData (filt2 U lam) U p := by sorry

end Arxiv1605_04704
