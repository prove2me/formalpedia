-- Prove2me | Theorems.Thm_DataTrackComp_Surplus_lemma_3_part_1
-- name    : DataTrackComp.Surplus.lemma_3_part_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:33.725987+00:00
-- url     : https://prove2.me/theorems/6334f3e4-2b8e-4fba-b0a7-112f97091a69
-- title:
--   Lemma 3 part 1, p. OA-5 — for m < m_L, G(m) has a unique PSNE, with p^A_1 > 0 and p^B_1 > p^A_1 − 1/2
-- statement:
--   Let $m>0$ with $m<m_L$, where $m_L=\sup\{m'>0:(0,m']\subseteq\mathcal E\}$ and $\mathcal E$ is the set of $m$ for which $\mathbf G(m)$ has an interior pure-strategy Nash equilibrium (B.32). Then $\mathbf G(m)$ has exactly one pure-strategy Nash equilibrium $(p^A_1,p^B_1)$, and it satisfies
--   $$p^A_1>0,\qquad p^B_1>p^A_1-\tfrac12.$$
--
--   This is the "interior equilibrium regime" in which Theorem 2 is stated. With Lemma 2, it gives existence and uniqueness of the forward-looking product-1 prices.
--
--   **Formalization Note.** "$m<m_L$" is the predicate `InInteriorRegime m` of the reduced-game file, which avoids `sSup`. Lemma 3's constant $m_H$ and its part 2 (the corner regime) are not part of this item.
-- source:
--   Bimpikis, Morgenstern & Saban, Data Tracking under Competition, authors' manuscript with online appendix (Operations Research, doi:10.1287/opre.2023.2489; PDF of 2023-05-04), p. OA-5 (PDF 40), Lemma 3 part 1; p. OA-18 (PDF 53), (B.32)

import Mathlib
import Definitions.Def_DataTrackComp_Surplus_ReducedGame

namespace DataTrackComp.Surplus

theorem lemma_3_part_1 (m : ℝ) (hm : 0 < m) (hmL : InInteriorRegime m) :
    (∃! p : ℝ × ℝ, IsPSNE m p.1 p.2) ∧ ∀ pA pB : ℝ, IsPSNE m pA pB → 0 < pA ∧ pA - 1 / 2 < pB := by sorry

end DataTrackComp.Surplus
