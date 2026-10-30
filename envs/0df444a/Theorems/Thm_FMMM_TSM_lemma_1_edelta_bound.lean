-- Prove2me | Theorems.Thm_FMMM_TSM_lemma_1_edelta_bound
-- name    : FMMM.TSM.lemma_1_edelta_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:28:29.495953+00:00
-- url     : https://prove2.me/theorems/a6005085-00fe-4985-aa54-ba268bdc4108
-- title:
--   Lemma 1: $|E_\delta| \le \frac23|A_{BR}| + \frac43|A_{BB}| + |A_B| + \frac13|A_R|$
-- statement:
--   Throughout §4.2 until the final proof of Theorem 5 the paper assumes $e_i = 1$ for every impression type: there are $n = |J|$ impression types and $n$ impressions are drawn i.i.d. uniformly from them.
--
--   Let $F = E_f$ be a maximum 2-matching of $E$ (the integral max flow of $G_f$) with a TSM colouring, and let $E_\delta$ be the edges from $A_S$ to $I_T$ of the reachability cut after the surgery. Then
--
--   $$|E_\delta| \le \frac23|A_{BR}| + \frac43|A_{BB}| + |A_B| + \frac13|A_R|.$$
--
--   The lemma links the cut edges, which control $\mathrm{OPT}$, to the ad classes, which control $\mathrm{ALG}$.
--
--   Differences from the source:
--   - encoding: integral maximum s–t flow of the boosted flow graph G_f (capacities 2, 1, 2) with unit-flow edge set E_f → a maximum 2-matching F of E (IsMaxTwoMatching E F), with E_f = F; reason: integral flows of G_f are exactly the subgraphs of E with all degrees ≤ 2 and the flow value is the number of edges; same objects
--   - encoding: the four colouring rules of §4.2.1 applied to the paths and cycles of E_f → IsTSMColoring F blue: an explicit decomposition of F into vertex-disjoint pieces (whole paths, cycles), each coloured by the rule of its type, with the starting point and orientation of each piece existential; red = F \ blue; reason: the existential orientation is exactly the freedom left by "alternating"; same set of colourings
--   - encoding: the reachability min cut of G_f and the surgery → cutAds, cutImps defined from residual reachability (residReach) and the surgery rule; reason: the paper's construction written out; same sets
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, Lemma 1, p. 8 (proof pp. 8–9)

import Mathlib
import Definitions.Def_FMMM_TSM_IsMaxTwoMatching
import Definitions.Def_FMMM_TSM_IsTSMColoring
import Definitions.Def_FMMM_TSM_adsWith
import Definitions.Def_FMMM_TSM_eDelta

namespace FMMM.TSM

/-- **Lemma 1: `|E_δ| ≤ (2/3)|A_BR| + (4/3)|A_BB| + |A_B| + (1/3)|A_R|`.**
Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating 1-1/e*,
arXiv:0905.4100v1, Lemma 1, p. 8 (proof pp. 8–9).

For a maximum 2-matching `F` of `E` with a TSM colouring `blue`, the cut edges `E_δ = eDelta E F`
satisfy the displayed bound, with `A_BR, A_BB, A_B, A_R = adsWith F blue b r` for
`(b, r) = (1, 1), (2, 0), (1, 0), (0, 1)`. -/
theorem lemma_1_edelta_bound {A J : Type} [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J]
    (E F blue : Finset (A × J)) (hF : IsMaxTwoMatching E F) (hc : IsTSMColoring F blue) :
    ((eDelta E F).card : ℝ) ≤
      2 / 3 * (adsWith F blue 1 1).card + 4 / 3 * (adsWith F blue 2 0).card +
        (adsWith F blue 1 0).card + 1 / 3 * (adsWith F blue 0 1).card := by sorry

end FMMM.TSM
