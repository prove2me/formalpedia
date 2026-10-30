-- Prove2me | Theorems.Thm_FMMM_TSM_cut_observations
-- name    : FMMM.TSM.cut_observations
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:25:57.307583+00:00
-- url     : https://prove2.me/theorems/f14f94ea-467f-44fb-bc8d-996a47fa1914
-- title:
--   §4.2.3, pp. 7–8: observations (i)–(iii) on $E_\delta$
-- statement:
--   Throughout §4.2 until the final proof of Theorem 5 the paper assumes $e_i = 1$ for every impression type: there are $n = |J|$ impression types and $n$ impressions are drawn i.i.d. uniformly from them.
--
--   Let $F = E_f$ be a maximum 2-matching of $E$ (the integral max flow of $G_f$), let $(S, T)$ be the reachability cut of its residual graph after the surgery, and let $E_\delta$ be the edges from $A_S$ to $I_T$. Then
--
--   1. $E_\delta \subseteq E_f$;
--   2. every impression type in $I_T$ is incident to at most one edge of $E_\delta$;
--   3. every ad in $A_S$ is incident to at most one edge of $E_\delta$.
--
--   In particular $E_\delta$ is a matching, which is what makes the cut edges amenable to a balls-in-bins count.
--
--   Differences from the source:
--   - encoding: integral maximum s–t flow of the boosted flow graph G_f (capacities 2, 1, 2) with unit-flow edge set E_f → a maximum 2-matching F of E (IsMaxTwoMatching E F), with E_f = F; reason: integral flows of G_f are exactly the subgraphs of E with all degrees ≤ 2 and the flow value is the number of edges; same objects
--   - encoding: the reachability min cut of G_f and the surgery → cutAds, cutImps defined from residual reachability (residReach) and the surgery rule; reason: the paper's construction written out; same sets
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, §4.2.3, pp. 7–8 (unnumbered observations (i)–(iii))

import Mathlib
import Definitions.Def_FMMM_TSM_IsMaxTwoMatching
import Definitions.Def_FMMM_TSM_cutAds
import Definitions.Def_FMMM_TSM_cutImps
import Definitions.Def_FMMM_TSM_eDelta

namespace FMMM.TSM

/-- **Observations (i)–(iii) on the cut edges `E_δ`.**
Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating 1-1/e*,
arXiv:0905.4100v1, §4.2.3, pp. 7–8 (unnumbered): "Some observations: (i) We have E_δ ⊆ E_f, since otherwise, if
some (a, i) ∈ E_δ has no flow across it, then i would be reachable from s, and would not be in the
set T. (And we did not introduce any such edges in our surgery.) (ii) All i ∈ I_T have at most one
incident edge in E_δ (follows from the surgery). (iii) All a ∈ A_S have at most one incident edge in
E_δ."

For a maximum 2-matching `F` of `E`: `E_δ ⊆ F`; every `j ∈ I_T` is incident to at most one edge
of `E_δ`; every `a ∈ A_S` is incident to at most one edge of `E_δ`. -/
theorem cut_observations {A J : Type} [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J]
    (E F : Finset (A × J)) (hF : IsMaxTwoMatching E F) :
    eDelta E F ⊆ F ∧
    (∀ j : J, j ∉ cutImps E F → ((eDelta E F).filter (fun e => e.2 = j)).card ≤ 1) ∧
    (∀ a : A, a ∈ cutAds E F → ((eDelta E F).filter (fun e => e.1 = a)).card ≤ 1) := by sorry

end FMMM.TSM
