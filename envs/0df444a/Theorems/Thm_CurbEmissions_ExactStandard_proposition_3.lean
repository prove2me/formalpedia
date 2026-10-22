-- Prove2me | Theorems.Thm_CurbEmissions_ExactStandard_proposition_3
-- name    : CurbEmissions.ExactStandard.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:18:21.493408+00:00
-- url     : https://prove2.me/theorems/8cebae11-9e92-4a40-97c7-c312e9a8e9cc
-- title:
--   Proposition 3, p. 19 — under condition (1) of Lemma A.1, exact-standard Nash bargaining succeeds at s∗e and lowers total emissions below the split market's
-- statement:
--   Let the standing assumptions hold, let $\bar x$ be the largest root of $\pi_{1D}(s^*_{1D})=\pi_{1U}(\frac{\bar u-x}{c-\gamma})$, and assume condition (1) of Lemma A.1. Then:
--   1. the base model has a split-market outcome, i.e. a base-model outcome $(s_1,D)$;
--   2. for every such outcome, take the disagreement point $D_1=\pi_1(s_1,D)$, $D_2=\pi_2(s_1,D)$ (eq. (5)) and let
--   $$s^*_e=\frac{2h_1[\bar u+b(c-\gamma)]-(c-\gamma)\bar u}{(c-\gamma)[4h_1-(c-\gamma)]}.$$
--   Then the exact-standard negotiation between $R_1$ and $R_2$ has a Nash bargaining solution; every Nash bargaining solution $(s_e,t_h)$ has $s_e=s^*_e$; the regulators' total utility at $s^*_e$ strictly exceeds $D_1+D_2$; and the total emissions when one product at $s^*_e$ is sold in both markets are strictly lower than the total emissions of the split-market outcome.
--
--   The proposition shows that negotiating an exact global standard unifies a split market and reduces total emissions.
--
--   **Formalization Note** The disagreement point is read off the base-model outcome itself rather than from Lemma A.1's closed form, so the statement does not presuppose Lemma A.1. The transfer $t_h$ is left uncharacterized, as in the paper (footnote 3).
-- source:
--   Han, Hu & Dawande, Curbing Emissions: Environmental Regulations and Product Offerings Across Markets, MSOM (authors' accepted manuscript, 2022-07-28), p. 19, Proposition 3

import Mathlib
import Definitions.Def_CurbEmissions_ExactStandard_Model

namespace CurbEmissions.ExactStandard

/-- Proposition 3, p. 19: under condition (1) of Lemma A.1 the base model has a split-market outcome;
for every such outcome `(s1, D)`, with disagreement point `D1 = π1(s1, D)`, `D2 = π2(s1, D)`, the Nash
bargaining solution of the exact-standard negotiation exists, every solution has standard
`s∗e = (2h1[ū + b(c−γ)] − (c−γ)ū)/((c−γ)[4h1 − (c−γ)])`, the regulators' total utility at `s∗e`
exceeds `D1 + D2`, and total emissions at `s∗e` are strictly lower than at the split-market outcome. -/
theorem proposition_3 (P : Params) (hP : Standing P) (xbar : ℝ)
    (hx : IsGreatest (xbarEqSet P) xbar) (hc : Cond1 P xbar) :
    (∃ s1, IsBaseEq P s1 .D) ∧
    ∀ s1, IsBaseEq P s1 .D →
      let D1 := pi1 P s1 .D
      let D2 := pi2 P s1 .D
      let se := (2 * P.h1 * (P.ubar + P.b * (P.c - P.gam)) - (P.c - P.gam) * P.ubar) /
                  ((P.c - P.gam) * (4 * P.h1 - (P.c - P.gam)))
      (NBS P D1 D2).Nonempty ∧
      (∀ q ∈ NBS P D1 D2, q.1 = se) ∧
      D1 + D2 < Th P se ∧
      emissions P se .U < emissions P s1 .D := by sorry

end CurbEmissions.ExactStandard
