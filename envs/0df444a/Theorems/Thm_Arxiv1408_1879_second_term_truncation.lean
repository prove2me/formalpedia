-- Prove2me | Theorems.Thm_Arxiv1408_1879_second_term_truncation
-- name    : Arxiv1408_1879.second_term_truncation
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T11:51:40.186479+00:00
-- url     : https://prove2.me/theorems/4fecb9d6-1081-4528-a3e9-966399222b1f
-- title:
--   Eqs. (14)-(15): truncation of the series at the second term (as proved)
-- statement:
--   Let $L$ be an invertible bounded operator and $R$ a bounded operator on a complex normed space, and let $\psi_i\in E$. The first two terms of the series (12) are $\tilde\psi=L^{-1}\psi_i$ (eq. 13) and $C=L^{-1}RL^{-1}\psi_i$ (eq. 15), and the second carries the sign $-1$. So the truncation of (12) after the second term is
--   $$\frac{\partial\psi}{\partial z}\cong\tilde\psi-C,\qquad C=L^{-1}RL^{-1}\psi_i=L^{-1}R\tilde\psi.$$
--
--   **Formalization Note** Eq. (14) is printed as $\partial\psi/\partial z\cong\tilde\psi+C$, with $C$ as in (15). This disagrees in sign with series (12), whose second term is $-L^{-1}RL^{-1}\psi_i$. The statement records the truncation of (12) as it is printed (as proved). The later eq. (19) agrees with this sign.
-- source:
--   M. Spivack and O. Rath Spivack, Rough surface backscatter and statistics via extended parabolic integral equation, arXiv:1408.1879v2 (2015), claim c005; Section 3.2, eqs. (12)-(15), PDF p. 6

import Mathlib
import Definitions.Def_Arxiv1408_1879_Basic

open MeasureTheory Filter Topology

namespace Arxiv1408_1879

theorem second_term_truncation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (L : E ≃L[ℂ] E) (R : E →L[ℂ] E) (ψi : E) :
    seriesTerm L R ψi 0 = firstApprox L ψi ∧
    seriesTerm L R ψi 1 = correctionTerm L R ψi ∧
    (∑ n ∈ Finset.range 2, (-1 : ℂ) ^ n • seriesTerm L R ψi n) =
      firstApprox L ψi - correctionTerm L R ψi ∧
    correctionTerm L R ψi = L.symm (R (firstApprox L ψi)) := by sorry

end Arxiv1408_1879
