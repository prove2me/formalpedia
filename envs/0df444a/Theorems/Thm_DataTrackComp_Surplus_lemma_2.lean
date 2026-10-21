-- Prove2me | Theorems.Thm_DataTrackComp_Surplus_lemma_2
-- name    : DataTrackComp.Surplus.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:25.665649+00:00
-- url     : https://prove2.me/theorems/c2f1a487-25e7-42f0-baeb-20ddfe5512c9
-- title:
--   Lemma 2, p. OA-5 — forward-looking equilibria ↔ pure-strategy Nash equilibria of G(m)
-- statement:
--   Let $\bar u>0$ and $m>0$. A price pair $(p^A_1,p^B_1)$ is a pure-strategy Nash equilibrium of the reduced game $\mathbf G(m)$ if and only if there is a perfect Bayesian equilibrium of the forward-looking setting whose product-1 prices are $(p^A_1,p^B_1)$:
--   $$(p^A_1,p^B_1)\in\mathrm{PSNE}(\mathbf G(m))\iff\exists\ \text{forward-looking equilibrium with prices }(p^A_1,p^B_1).$$
--
--   Both directions of the lemma are included. Through it, existence, uniqueness and every property of the forward-looking equilibrium prices reduce to the two-player game $\mathbf G(m)$.
-- source:
--   Bimpikis, Morgenstern & Saban, Data Tracking under Competition, authors' manuscript with online appendix (Operations Research, doi:10.1287/opre.2023.2489; PDF of 2023-05-04), p. OA-5 (PDF 40), Lemma 2

import Mathlib
import Definitions.Def_DataTrackComp_Surplus_Game
import Definitions.Def_DataTrackComp_Surplus_ReducedGame

namespace DataTrackComp.Surplus

theorem lemma_2 (ubar m pA pB : ℝ) (hu : 0 < ubar) (hm : 0 < m) :
    IsPSNE m pA pB ↔ ∃ E : Assessment, IsEquilibrium .forward ubar m E ∧ E.pA = pA ∧ E.pB = pB := by sorry

end DataTrackComp.Surplus
