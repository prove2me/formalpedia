-- Prove2me | Theorems.Thm_FMMM_TSM_eq_3_cut_value
-- name    : FMMM.TSM.eq_3_cut_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:26:32.096385+00:00
-- url     : https://prove2.me/theorems/055cb39d-8b9e-40bf-b4c7-2660433f3562
-- title:
--   Eq. (3): $|E_f| = 2(|A_T| + |I_S|) + |E_\delta|$
-- statement:
--   Throughout §4.2 until the final proof of Theorem 5 the paper assumes $e_i = 1$ for every impression type: there are $n = |J|$ impression types and $n$ impressions are drawn i.i.d. uniformly from them.
--
--   Let $F = E_f$ be a maximum 2-matching of $E$ (the integral max flow of $G_f$), and let $(S, T)$ be the reachability cut after the surgery, with $A_T$ the ads on the sink side, $I_S$ the impression types on the source side and $E_\delta$ the edges from $A_S$ to $I_T$. By max-flow–min-cut,
--
--   $$|E_f| = 2(|A_T| + |I_S|) + |E_\delta|. \qquad (3)$$
--
--   Differences from the source:
--   - encoding: integral maximum s–t flow of the boosted flow graph G_f (capacities 2, 1, 2) with unit-flow edge set E_f → a maximum 2-matching F of E (IsMaxTwoMatching E F), with E_f = F; reason: integral flows of G_f are exactly the subgraphs of E with all degrees ≤ 2 and the flow value is the number of edges; same objects
--   - encoding: the reachability min cut of G_f and the surgery → cutAds, cutImps defined from residual reachability (residReach) and the surgery rule; reason: the paper's construction written out; same sets
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, §4.2.3, p. 8, eq. (3)

import Mathlib
import Definitions.Def_FMMM_TSM_IsMaxTwoMatching
import Definitions.Def_FMMM_TSM_cutAds
import Definitions.Def_FMMM_TSM_cutImps
import Definitions.Def_FMMM_TSM_eDelta

namespace FMMM.TSM

/-- **Equation (3): `|E_f| = 2(|A_T| + |I_S|) + |E_δ|`.**
Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating 1-1/e*,
arXiv:0905.4100v1, §4.2.3, p. 8, eq. (3): "The min-cut of G_f is made up of the edges E_δ, the |A_T| edges from s
to A_T (with capacity 2), and the |I_S| edges from I_S to t (also capacity 2). Thus, by
max-flow-min-cut, we have |E_f| = 2(|A_T| + |I_S|) + |E_δ|."

For a maximum 2-matching `F` of `E`, with `A_T = A \ cutAds E F`, `I_S = cutImps E F` and
`E_δ = eDelta E F`. -/
theorem eq_3_cut_value {A J : Type} [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J]
    (E F : Finset (A × J)) (hF : IsMaxTwoMatching E F) :
    F.card = 2 * ((Finset.univ \ cutAds E F).card + (cutImps E F).card) + (eDelta E F).card := by sorry

end FMMM.TSM
