-- Prove2me | Theorems.Thm_Arxiv1605_04704_case_b1_spectral_decomposition
-- name    : Arxiv1605_04704.case_b1_spectral_decomposition
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T21:10:04.892804+00:00
-- url     : https://prove2.me/theorems/184b6f40-42f4-47d8-82a1-3770c0bb5121
-- title:
--   Section 5, case b.1, eqs. (25)-(26): spectral decomposition of the filtered matrix for q = 3, r = 4
-- statement:
--   Let $M_{\exp}$ be a real $4\times4$ matrix and $H(M_{\exp})=U\operatorname{diag}(\lambda_{\exp,0},\dots,\lambda_{\exp,3})U^\dagger$ with $U$ unitary and $\lambda_{\exp,0}\ge\dots\ge\lambda_{\exp,3}$, $\lambda_{\exp,0}>0$. Let $H_{\mathrm{cov}}$, $M_{\mathrm{cov}}$, its normalized eigenvalues $\hat\lambda_i$, its indices of purity $P_i$, its $m_{00}$ and its components $M_{Ui},M_2,M_3,M_{\Delta0}$ be those of the covariance filtering (eq. 23), and let $r=\operatorname{rank}H_{\mathrm{cov}}$. Assume $r=4$ and $P_3>0$, and let $M_f=[M_{\mathrm{cov}}-(1-P_3)M_{\Delta0}]/P_3$ (eq. 24). Put
--
--   $$p_i=\frac{\hat\lambda_i-\hat\lambda_3}{1-4\hat\lambda_3}\quad(i=0,1,2).$$
--
--   Then
--
--   $$M_f=p_0M_{U0}+p_1M_{U1}+p_2M_{U2},$$
--
--   where $M_{Ui}$ are the spectral components of $M_{\mathrm{cov}}$, and
--
--   $$p_0=\tfrac13\Big(1+\tfrac{P_2}{2P_3}+\tfrac{3P_1}{2P_3}\Big),\quad p_1=\tfrac13\Big(1+\tfrac{P_2}{2P_3}-\tfrac{3P_1}{2P_3}\Big),\quad p_2=\tfrac13\Big(1-\tfrac{P_2}{P_3}\Big).$$
--
--   The sum is convex ($p_i\ge0$, $p_0+p_1+p_2=1$), and it is the spectral decomposition of $M_f$. That is, $M_f$ has the same $m_{00}$ as $M_{\mathrm{cov}}$, and $H(M_f)=m_{00}U\operatorname{diag}(p_0,p_1,p_2,0)U^\dagger$ with $p_0\ge p_1\ge p_2\ge0$.
--
--   This is eqs. (25)-(26), the filtered estimate of a sample hypothesized to have three components.
--
--   **Formalization Note** The hypothesis $P_3>0$ is not written in the paper. It makes the division in (24) and (26) meaningful. "Spectral decomposition of $M_f$" is stated as: $(U,(p_0,p_1,p_2,0))$ is ordered spectral data for $M_f$ in the sense of eqs. (3)-(4).
--
--   **Formalization Note** The paper asks for $\lambda_{\mathrm{cov},0}=\lambda_0$ (the largest eigenvalue is not replaced), otherwise the measurement is rejected. The statement assumes $\lambda_{\exp,0}>0$, which also excludes $H_{\mathrm{cov}}=0$, where the normalization $\hat\lambda_i=\lambda_{\mathrm{cov},i}/\operatorname{tr}H_{\mathrm{cov}}$ is undefined.
-- source:
--   J. J. Gil, On optimal filtering of measured Mueller matrices, arXiv:1605.04704v3 (2016), claim c019; Section 5, case b.1 (q = 3, r = 4), eqs. (24)-(26), right column of PDF p. 4

import Mathlib
import Definitions.Def_Arxiv1605_04704_Basic

open Matrix
open scoped ComplexOrder

namespace Arxiv1605_04704

theorem case_b1_spectral_decomposition (Mexp : Matrix (Fin 4) (Fin 4) ℝ) (U : Matrix.unitaryGroup (Fin 4) ℂ) (lam : Fin 4 → ℝ)
    (hdat : IsCovFilterData Mexp U lam) (hlam0 : 0 < lam 0)
    (hr : (covH U lam).rank = 4) (hP3 : 0 < ipp3 (covLhat lam)) :
    let l := covLhat lam
    let c := covMueller U lam 0 0
    let p : Fin 4 → ℝ := ![(l 0 - l 3) / (1 - 4 * l 3), (l 1 - l 3) / (1 - 4 * l 3),
      (l 2 - l 3) / (1 - 4 * l 3), 0]
    filt3 U lam = p 0 • specComp U c 0 + p 1 • specComp U c 1 + p 2 • specComp U c 2 ∧
    p 0 = (1 / 3) * (1 + ipp2 l / (2 * ipp3 l) + 3 * ipp1 l / (2 * ipp3 l)) ∧
    p 1 = (1 / 3) * (1 + ipp2 l / (2 * ipp3 l) - 3 * ipp1 l / (2 * ipp3 l)) ∧
    p 2 = (1 / 3) * (1 - ipp2 l / ipp3 l) ∧
    (∀ i, 0 ≤ p i) ∧ p 0 + p 1 + p 2 = 1 ∧
    filt3 U lam 0 0 = c ∧ IsSpectralData (filt3 U lam) U p := by sorry

end Arxiv1605_04704
