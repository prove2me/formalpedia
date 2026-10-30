-- Prove2me | Theorems.Thm_FMMM_TSM_opt_le_scenario_cut
-- name    : FMMM.TSM.opt_le_scenario_cut
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:27:16.832034+00:00
-- url     : https://prove2.me/theorems/ad64ed42-56a8-44d5-9ab5-49d36398e988
-- title:
--   §4.2.3, p. 8: $\mathrm{OPT} \le |\hat I_S| + |A_T| + |A^*_\delta|$
-- statement:
--   Throughout §4.2 until the final proof of Theorem 5 the paper assumes $e_i = 1$ for every impression type: there are $n = |J|$ impression types and $n$ impressions are drawn i.i.d. uniformly from them.
--
--   Let $F = E_f$ be a maximum 2-matching of $E$ with the cut $(S, T)$ after the surgery. For every sequence of $n$ arrivals, let $|\hat I_S|$ be the number of draws whose type lies in $I_S$ (counted with multiplicity) and $A^*_\delta$ the ads of $E_\delta$ adjacent to a drawn impression of $I_T$. Then
--
--   $$\mathrm{OPT} \le |\hat I_S| + |A_T| + |A^*_\delta|.$$
--
--   The bound is deterministic: it is the capacity of the cut $\hat S = \hat I_S \cup (A_S \setminus A^*_\delta)$, $\hat T = \hat I_T \cup A_T \cup A^*_\delta$ of the realization graph.
--
--   Differences from the source:
--   - encoding: integral maximum s–t flow of the boosted flow graph G_f (capacities 2, 1, 2) with unit-flow edge set E_f → a maximum 2-matching F of E (IsMaxTwoMatching E F), with E_f = F; reason: integral flows of G_f are exactly the subgraphs of E with all degrees ≤ 2 and the flow value is the number of edges; same objects
--   - encoding: the reachability min cut of G_f and the surgery → cutAds, cutImps defined from residual reachability (residReach) and the surgery rule; reason: the paper's construction written out; same sets
--   - encoding: Î_S = ∪_{i∈I_S} D(i), the set of drawn impressions of types in I_S → the number of draws t with ω t ∈ I_S; reason: draws are the impressions of the scenario; same count
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, §4.2.3, p. 8 (unnumbered)

import Mathlib
import Definitions.Def_FMMM_TSM_IsMaxTwoMatching
import Definitions.Def_FMMM_TSM_realOPT
import Definitions.Def_FMMM_TSM_cutAds
import Definitions.Def_FMMM_TSM_cutImps
import Definitions.Def_FMMM_TSM_aStarDelta

namespace FMMM.TSM

/-- **The scenario cut bound `OPT ≤ |Î_S| + |A_T| + |A*_δ|`.**
Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating 1-1/e*,
arXiv:0905.4100v1, §4.2.3, p. 8 (unnumbered): "We set Ŝ = Î_S ∪ (A_S \ A*_δ) and T̂ = Î_T ∪ A_T ∪ A*_δ. Now we will
measure the size of the cut (Ŝ, T̂) in Ĝ_f. … But note that there are no edges in G_f from A ∩ Ŝ to
Î_T, since we got rid of them in our surgery. Thus we have OPT ≤ |Î_S| + |A_T| + |A*_δ|."

Unit instance: for a maximum 2-matching `F` of `E` and every arrival sequence
`ω : Fin |J| → J`, `OPT(ω) ≤ #{t : ω t ∈ I_S} + |A_T| + |A*_δ(ω)|`. -/
theorem opt_le_scenario_cut {A J : Type} [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J]
    (E F : Finset (A × J)) (hF : IsMaxTwoMatching E F) (ω : Fin (Fintype.card J) → J) :
    realOPT E ω ≤ (Finset.univ.filter (fun t => ω t ∈ cutImps E F)).card +
      (Finset.univ \ cutAds E F).card + (aStarDelta E F ω).card := by sorry

end FMMM.TSM
