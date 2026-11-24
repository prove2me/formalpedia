-- Prove2me | Theorems.Thm_Arxiv1605_04704_spectral_weights_extremal
-- name    : Arxiv1605_04704.spectral_weights_extremal
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T20:18:33.940513+00:00
-- url     : https://prove2.me/theorems/f2e82e2b-222c-4ede-8ed2-b9ddcb6547fa
-- title:
--   Section 2, after eq. (8): the spectral weights bound the coefficients of every arbitrary decomposition
-- statement:
--   Let $M$ be a real $4\times4$ matrix with $m_{00}>0$ satisfying the covariance criterion, let $r=\operatorname{rank}H(M)$, and let $\hat\lambda_0\ge\dots\ge\hat\lambda_3$ be the normalized eigenvalues of $H(M)$. For every arbitrary decomposition $H(M)=\sum_{i=0}^{r-1}p_i\,m_{00}\,w_i\otimes w_i^\dagger$ (eq. 6) and every $i$,
--
--   $$\hat\lambda_{r-1}\le p_i\le\hat\lambda_0 .$$
--
--   Both bounds are attained, by the spectral decomposition (8). Hence $\hat\lambda_0$ is the maximum relative weight of a pure component over all arbitrary decompositions of $M$, and $\hat\lambda_{r-1}$ is the minimum.
--
--   The paper applies this to $M_{\mathrm{cov}}$ (Section 5) and to $M_f$ (Sections 7-8). For $r=4$ the minimum is $\hat\lambda_3$.
--
--   **Formalization Note** The statement is written as "the set of all coefficients $p_i$ of all arbitrary decompositions has greatest element $\hat\lambda_0$ and least element $\hat\lambda_{r-1}$". The paper also says that "the equalities hold only for the spectral decomposition". That part is false for $r\ge3$ and is not included (see the mission description).
-- source:
--   J. J. Gil, On optimal filtering of measured Mueller matrices, arXiv:1605.04704v3 (2016), claim c001; Section 2, paragraph after eq. (8), PDF p. 2; restated in Section 5 (left column) PDF p. 4, Section 7 PDF p. 5, Section 8 around eq. (35) PDF p. 6

import Mathlib
import Definitions.Def_Arxiv1605_04704_Basic

open Matrix
open scoped ComplexOrder

namespace Arxiv1605_04704

theorem spectral_weights_extremal (M : Matrix (Fin 4) (Fin 4) ℝ) (hm : 0 < M 0 0)
    (hpsd : (cohMat M).PosSemidef) (U : Matrix.unitaryGroup (Fin 4) ℂ) (l : Fin 4 → ℝ)
    (hs : IsSpectralData M U l) :
    IsGreatest {x : ℝ | ∃ (p : Fin (cohMat M).rank → ℝ) (w : Fin (cohMat M).rank → Fin 4 → ℂ),
        IsArbitraryDecomp M p w ∧ ∃ i, p i = x} (l 0) ∧
    ∀ j : Fin 4, (j : ℕ) + 1 = (cohMat M).rank →
      IsLeast {x : ℝ | ∃ (p : Fin (cohMat M).rank → ℝ) (w : Fin (cohMat M).rank → Fin 4 → ℂ),
        IsArbitraryDecomp M p w ∧ ∃ i, p i = x} (l j) := by sorry

end Arxiv1605_04704
