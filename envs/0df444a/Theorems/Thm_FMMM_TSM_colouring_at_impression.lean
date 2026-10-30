-- Prove2me | Theorems.Thm_FMMM_TSM_colouring_at_impression
-- name    : FMMM.TSM.colouring_at_impression
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:23:21.788504+00:00
-- url     : https://prove2.me/theorems/bf584a1e-ee24-4b84-bc9d-572c54854099
-- title:
--   §4.2.1, p. 7: coloured edges at an impression
-- statement:
--   Throughout §4.2 until the final proof of Theorem 5 the paper assumes $e_i = 1$ for every impression type: there are $n = |J|$ impression types and $n$ impressions are drawn i.i.d. uniformly from them.
--
--   Let $F$ be the edge set of an integral maximum flow of the boosted flow graph $G_f$ (equivalently, a maximum 2-matching of $E$) and colour it by the rules of the two suggested matchings algorithm. Then every impression type $j$ is incident to
--
--   1. no coloured edge, or
--   2. exactly one blue edge and no red edge, or
--   3. exactly one blue edge and exactly one red edge.
--
--   This guarantees that the online phase, which follows the blue edge of a type at its first arrival and the red edge at its second, is well defined.
--
--   Differences from the source:
--   - encoding: integral maximum s–t flow of the boosted flow graph G_f (capacities 2, 1, 2) with unit-flow edge set E_f → a maximum 2-matching F of E (IsMaxTwoMatching E F), with E_f = F; reason: integral flows of G_f are exactly the subgraphs of E with all degrees ≤ 2 and the flow value is the number of edges; same objects
--   - encoding: the four colouring rules of §4.2.1 applied to the paths and cycles of E_f → IsTSMColoring F blue: an explicit decomposition of F into vertex-disjoint pieces (whole paths, cycles), each coloured by the rule of its type, with the starting point and orientation of each piece existential; red = F \ blue; reason: the existential orientation is exactly the freedom left by "alternating"; same set of colourings
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, §4.2.1, p. 7 (unnumbered remark after the colouring rules)

import Mathlib
import Definitions.Def_FMMM_TSM_IsMaxTwoMatching
import Definitions.Def_FMMM_TSM_IsTSMColoring

namespace FMMM.TSM

/-- **Coloured edges at an impression.**
Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating 1-1/e*,
arXiv:0905.4100v1, §4.2.1, p. 7 (unnumbered): "Note that all i ∈ I are incident to either no colored edges, one
blue edge, or a blue and a red edge."

For a maximum 2-matching `F` of `E` (the integral max flow) coloured by the TSM rules, every
impression type `j` has (0 blue, 0 red), (1 blue, 0 red) or (1 blue, 1 red) incident edges. -/
theorem colouring_at_impression {A J : Type} [DecidableEq A] [DecidableEq J]
    (E F blue : Finset (A × J)) (hF : IsMaxTwoMatching E F) (hc : IsTSMColoring F blue) (j : J) :
    ((blue.filter (fun e => e.2 = j)).card = 0 ∧ ((F \ blue).filter (fun e => e.2 = j)).card = 0) ∨
    ((blue.filter (fun e => e.2 = j)).card = 1 ∧ ((F \ blue).filter (fun e => e.2 = j)).card = 0) ∨
    ((blue.filter (fun e => e.2 = j)).card = 1 ∧ ((F \ blue).filter (fun e => e.2 = j)).card = 1) := by sorry

end FMMM.TSM
