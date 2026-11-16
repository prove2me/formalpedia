-- Prove2me | Theorems.Thm_CanadaCTP_Supplement_theorem_2
-- name    : CanadaCTP.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T17:39:39.255616+00:00
-- url     : https://prove2.me/theorems/6bb908f5-45ad-4aed-b6e3-1e9b6e6ef92f
-- title:
--   Theorem 2 — deciding whether a first edge is optimal is NP-hard and coNP-hard on two-edge-path graphs
-- statement:
--   Consider CTP on disjoint-path graphs where each path consists of two edges. Deciding whether it is optimal for the agent to travel along a certain edge in the first step is both NP-hard and coNP-hard.
--
--   Precisely: the first-move language of disjoint-path instances whose paths all have two edges (codes of an instance and an edge such that some optimal adaptive policy traverses that edge as its first move) is NP-hard and coNP-hard.
--
--   The coNP half shows that the problem is unlikely to lie in NP: a short certificate for "this first move is optimal" would give NP = coNP.
--
--   Differences from the source:
--   - encoding: the decision problem on explicitly given instances and a given edge → a language of strings over a 7-letter alphabet: binary codes of rational instances (value and probability as numerator/denominator pairs) plus an edge (i, j); non-codes and invalid lists are not in it; reason: the standard encoding of an explicit finite input; the reduction's instances (Definition 10) are rational
--   - encoding: NP-hard (no machine model named) → every language in CookPvsNP.NP over every finite nonempty alphabet is polynomial-time many-one reducible to it (published CookPvsNP_defs); reason: the standard notion of NP-hardness
--   - encoding: a policy traverses the edge as its first move → the edge is a first edge (j = 0) and, almost surely, whenever the second edge of some path is revealed the second edge of path i is (TraversesFirst); reason: on instances whose paths all have two edges the first traversal from s is exactly what reveals a second edge
--   - encoding: optimal adaptive policy (deterministic, history-dependent) → feasible randomized stateful policy with expCost = optCost (the published CanadaCTP.optCost); reason: the randomized stateful class contains the paper's policies and no mixture beats its best component, so the optimum and the optimal deterministic policies are the same
--   - reading: it is optimal for the agent to travel along a certain edge in the first step → there exists an optimal adaptive policy whose first move is that edge; reason: §4 (p.20) states Theorem 2 in exactly this form
-- source:
--   Abels–Pitschmann–Schewior–Schmand, Canada Retravelled (manuscript, STOC 2027 submission, sha256 8117348eb78ba082edf376778214fa414f31cb0cd8a8d06c12a1dfba627e3a33), Theorem 2, p.29 (first stated p.4); §4, p.20; Theorem 6, p.26; Corollary 1, p.28 (proof in Appendix D)

import Mathlib
import Definitions.Def_CanadaCTP_Supplement_FirstMove

namespace CanadaCTP.Supplement

/-- Abels–Pitschmann–Schewior–Schmand, *Canada Retravelled* (manuscript, sha256 8117348e…3a33),
Theorem 2, p.29 (first stated p.4): "Consider CTP on disjoint-path graphs where each path consists
of two edges. Deciding whether it is optimal for the agent to travel along a certain edge in the
first step is both NP-hard and coNP-hard."

The language of codes of (instance, edge) queries on disjoint-path instances whose paths all have
two edges, such that some optimal adaptive policy traverses the edge in its first step, is both
NP-hard and coNP-hard (polynomial-time many-one reductions from every NP, resp. coNP, language
over every finite nonempty alphabet).

**Formalization Note.** "It is optimal to travel along the edge in the first step" is read as in
§4 (p.20) and Theorem 6: there exists an optimal adaptive policy whose first move is that edge.
The language is `firstMoveLang TwoEdgeClass`; NP, coNP and reductions are the published
`CookPvsNP` ones. -/
theorem theorem_2 :
    NPHard (firstMoveLang TwoEdgeClass) ∧ CoNPHard (firstMoveLang TwoEdgeClass) := by sorry

end CanadaCTP.Supplement
