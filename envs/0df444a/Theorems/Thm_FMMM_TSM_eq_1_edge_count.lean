-- Prove2me | Theorems.Thm_FMMM_TSM_eq_1_edge_count
-- name    : FMMM.TSM.eq_1_edge_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:24:35.630956+00:00
-- url     : https://prove2.me/theorems/34428c69-c348-491f-ac87-aeaeba78e232
-- title:
--   Eq. (1): $|E_f| = 2A_{BR} + 2A_{BB} + A_B + A_R$
-- statement:
--   Throughout §4.2 until the final proof of Theorem 5 the paper assumes $e_i = 1$ for every impression type: there are $n = |J|$ impression types and $n$ impressions are drawn i.i.d. uniformly from them.
--
--   Let $F = E_f$ be a maximum 2-matching of $E$ (the integral max flow of $G_f$) with a TSM colouring, and let $A_{BR}, A_{BB}, A_B, A_R$ be the ads incident to (one blue and one red), (two blue), (only one blue), (only one red) edges. Then
--
--   $$|E_f| = 2|A_{BR}| + 2|A_{BB}| + |A_B| + |A_R|.$$
--
--   Combined with the cut value (3), it converts the bound on $\mathrm{OPT}$ into the same coordinates as the bound on $\mathrm{ALG}$.
--
--   Differences from the source:
--   - encoding: integral maximum s–t flow of the boosted flow graph G_f (capacities 2, 1, 2) with unit-flow edge set E_f → a maximum 2-matching F of E (IsMaxTwoMatching E F), with E_f = F; reason: integral flows of G_f are exactly the subgraphs of E with all degrees ≤ 2 and the flow value is the number of edges; same objects
--   - encoding: the four colouring rules of §4.2.1 applied to the paths and cycles of E_f → IsTSMColoring F blue: an explicit decomposition of F into vertex-disjoint pieces (whole paths, cycles), each coloured by the rule of its type, with the starting point and orientation of each piece existential; red = F \ blue; reason: the existential orientation is exactly the freedom left by "alternating"; same set of colourings
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, §4.2.2, p. 7, eq. (1)

import Mathlib
import Definitions.Def_FMMM_TSM_IsMaxTwoMatching
import Definitions.Def_FMMM_TSM_IsTSMColoring
import Definitions.Def_FMMM_TSM_adsWith

namespace FMMM.TSM

/-- **Equation (1): `|E_f| = 2A_BR + 2A_BB + A_B + A_R`.**
Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating 1-1/e*,
arXiv:0905.4100v1, §4.2.2, p. 7, eq. (1).

For a maximum 2-matching `F` of `E` with a TSM colouring `blue`,
`|F| = 2|A_BR| + 2|A_BB| + |A_B| + |A_R|`, where the classes are `adsWith F blue b r` with
`(b, r) = (1, 1), (2, 0), (1, 0), (0, 1)`. -/
theorem eq_1_edge_count {A J : Type} [Fintype A] [DecidableEq A] [DecidableEq J]
    (E F blue : Finset (A × J)) (hF : IsMaxTwoMatching E F) (hc : IsTSMColoring F blue) :
    F.card = 2 * (adsWith F blue 1 1).card + 2 * (adsWith F blue 2 0).card +
      (adsWith F blue 1 0).card + (adsWith F blue 0 1).card := by sorry

end FMMM.TSM
