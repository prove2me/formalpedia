-- Prove2me | Theorems.Thm_Arxiv1605_04704_case_a_four_components
-- name    : Arxiv1605_04704.case_a_four_components
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T20:41:19.230956+00:00
-- url     : https://prove2.me/theorems/c1f02ee1-2b7c-4a6b-b667-ea8176d0ff7d
-- title:
--   Section 5, case a (q = 4): four is the maximum, and r < 4 excludes four components
-- statement:
--   Let $M_{\exp}$ be a real $4\times4$ matrix and $H(M_{\exp})=U\operatorname{diag}(\lambda_{\exp,0},\dots,\lambda_{\exp,3})U^\dagger$ with $U$ unitary and $\lambda_{\exp,0}\ge\dots\ge\lambda_{\exp,3}$, $\lambda_{\exp,0}>0$. Let $H_{\mathrm{cov}}$, $M_{\mathrm{cov}}$, its normalized eigenvalues $\hat\lambda_i$, its indices of purity $P_i$, its $m_{00}$ and its components $M_{Ui},M_2,M_3,M_{\Delta0}$ be those of the covariance filtering (eq. 23), and let $r=\operatorname{rank}H_{\mathrm{cov}}$. Then:
--
--   1. every decomposition of $M_{\mathrm{cov}}$ into $n$ pure components with positive weights and linearly independent covariance vectors has $n\le4$;
--   2. if $r<4$, $M_{\mathrm{cov}}$ has no such decomposition with $n=4$, so the hypothesis $q=4$ does not match the measurement.
--
--   **Formalization Note** The procedural part of case a ("the covariance filtering itself completes the process") is not a mathematical statement and is not formalized.
--
--   **Formalization Note** The paper asks for $\lambda_{\mathrm{cov},0}=\lambda_0$ (the largest eigenvalue is not replaced), otherwise the measurement is rejected. The statement assumes $\lambda_{\exp,0}>0$, which also excludes $H_{\mathrm{cov}}=0$, where the normalization $\hat\lambda_i=\lambda_{\mathrm{cov},i}/\operatorname{tr}H_{\mathrm{cov}}$ is undefined.
-- source:
--   J. J. Gil, On optimal filtering of measured Mueller matrices, arXiv:1605.04704v3 (2016), claim c017; Section 5, case a, right column of PDF p. 4

import Mathlib
import Definitions.Def_Arxiv1605_04704_Basic

open Matrix
open scoped ComplexOrder

namespace Arxiv1605_04704

theorem case_a_four_components (Mexp : Matrix (Fin 4) (Fin 4) ℝ) (U : Matrix.unitaryGroup (Fin 4) ℂ) (lam : Fin 4 → ℝ)
    (hdat : IsCovFilterData Mexp U lam) (hlam0 : 0 < lam 0) :
    (∀ (n : ℕ) (p : Fin n → ℝ) (w : Fin n → Fin 4 → ℂ),
        IsPureDecomp (covMueller U lam) n p w → (∀ i, 0 < p i) → n ≤ 4) ∧
    ((covH U lam).rank < 4 → ¬ ∃ (p : Fin 4 → ℝ) (w : Fin 4 → Fin 4 → ℂ),
        IsPureDecomp (covMueller U lam) 4 p w ∧ ∀ i, 0 < p i) := by sorry

end Arxiv1605_04704
