-- Prove2me | Theorems.Thm_CurbEmissions_ExactStandard_proposition_2_split
-- name    : CurbEmissions.ExactStandard.proposition_2_split
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:27.259487+00:00
-- url     : https://prove2.me/theorems/caaa7cbf-de36-474a-8cbd-a9843494ad33
-- title:
--   Proposition 2 (split-market half), p. 16 — a split-market base outcome has higher total emissions than the arbitrator outcome
-- statement:
--   Let the standing assumptions hold. If $(s_1,D)$ is a base-model outcome, so the firm offers differentiated products, then the total emissions of that outcome strictly exceed the total emissions of the arbitrator outcome, in which one product with efficiency level $s^*_a$ is sold in both markets:
--   $$\sum_{i}(b-s^*_a)\frac{m_i}{2\bar u}[\bar u-(c-\gamma)s^*_a]\;<\;(b-s_1)\frac{m_1}{2\bar u}[\bar u-(c-\gamma)s_1]+\frac12 bm_2 .$$
--
--   This is the half of Proposition 2 that concerns split markets; it motivates unifying a split market as a way to lower emissions.
--
--   **Formalization Note** "In its domain" is read as "whenever a base-model outcome has the firm playing $D$". The half of Proposition 2 about unified outcomes is not part of this mission.
-- source:
--   Han, Hu & Dawande, Curbing Emissions: Environmental Regulations and Product Offerings Across Markets, MSOM (authors' accepted manuscript, 2022-07-28), p. 16, Proposition 2 (second sentence)

import Mathlib
import Definitions.Def_CurbEmissions_ExactStandard_Model

namespace CurbEmissions.ExactStandard

/-- Proposition 2 (split-market half), p. 16: every base-model outcome in which the firm plays D has
strictly higher total emissions than the arbitrator outcome (a unified product at `s∗a`). -/
theorem proposition_2_split (P : Params) (hP : Standing P) :
    ∀ s1, IsBaseEq P s1 .D → emissions P (saStar P) .U < emissions P s1 .D := by sorry

end CurbEmissions.ExactStandard
