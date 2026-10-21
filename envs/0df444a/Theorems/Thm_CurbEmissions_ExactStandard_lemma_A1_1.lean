-- Prove2me | Theorems.Thm_CurbEmissions_ExactStandard_lemma_A1_1
-- name    : CurbEmissions.ExactStandard.lemma_A1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:14.493979+00:00
-- url     : https://prove2.me/theorems/11c8e3ae-592c-4a44-8c2a-fd605abf6691
-- title:
--   Lemma A.1(1), Online Appendix p. 1 (PDF 33) — under condition (1), s∗1 = s∗1D and the firm offers differentiated products
-- statement:
--   Let the standing assumptions hold, let $\bar x$ be the largest root of $\pi_{1D}(s^*_{1D})=\pi_{1U}(\frac{\bar u-x}{c-\gamma})$, and assume condition (1):
--   $$0<r\le\min\Big\{\frac{m_2\bar u}{4}-\frac{m_2[\bar u-b(c-\gamma)]^2}{\bar u(4-\frac{c-\gamma}{h_1})^2},\ \frac{m_1[\bar u-b(c-\gamma)]^2}{\bar u(4-\frac{c-\gamma}{h_1})^2},\ \frac{m_2}{4\bar u}(\bar u^2-\bar x^2)\Big\}.$$
--   Then
--   1. $(s^*_{1D}, D)$ is a base-model outcome, where $s^*_{1D}=\frac{2h_1\bar u-(c-\gamma)(\bar u-2h_1b)}{(c-\gamma)[4h_1-(c-\gamma)]}$: $R_1$ sets $s_1^*=s^*_{1D}$ and the firm offers differentiated products;
--   2. every base-model outcome in which the firm offers differentiated products has standard $s_1=s^*_{1D}$.
--
--   This is the split-market case of the base model, and it supplies the disagreement point of the negotiation in Proposition 3.
--
--   **Formalization Note** The statement does not claim that every base-model outcome is $(s^*_{1D},D)$: when condition (1) holds with equality, a unified outcome can give $R_1$ the same utility, and the paper's sufficient condition does not exclude that tie.
-- source:
--   Han, Hu & Dawande, Curbing Emissions: Environmental Regulations and Product Offerings Across Markets, MSOM (authors' accepted manuscript, 2022-07-28), Online Appendix p. 1 (PDF 33), Lemma A.1(1)

import Mathlib
import Definitions.Def_CurbEmissions_ExactStandard_Model

namespace CurbEmissions.ExactStandard

/-- Lemma A.1(1), Online Appendix p. 1: under condition (1), `(s∗1D, D)` is a base-model outcome, and
every base-model outcome in which the firm plays D has `s1 = s∗1D`. -/
theorem lemma_A1_1 (P : Params) (hP : Standing P) (xbar : ℝ)
    (hx : IsGreatest (xbarEqSet P) xbar) (hc : Cond1 P xbar) :
    IsBaseEq P (s1DStar P) .D ∧ ∀ s1, IsBaseEq P s1 .D → s1 = s1DStar P := by sorry

end CurbEmissions.ExactStandard
