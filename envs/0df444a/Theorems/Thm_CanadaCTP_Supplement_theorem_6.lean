-- Prove2me | Theorems.Thm_CanadaCTP_Supplement_theorem_6
-- name    : CanadaCTP.Supplement.theorem_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T17:38:49.782937+00:00
-- url     : https://prove2.me/theorems/269344fc-841d-4255-a49b-398534361443
-- title:
--   Theorem 6 — deciding whether an optimal policy can take a given first edge is NP-hard (two-edge paths, constant first edges, supports $\le3$)
-- statement:
--   Deciding whether there exists an optimal adaptive policy that traverses a given edge as its first move in the Stochastic Canadian Traveller Problem is NP-hard, even on disjoint-path graphs in which every path has length $2$, the weight of every first edge is constant and the weight of every second edge has a support of size at most $3$.
--
--   Precisely: the first-move language of this class of instances is NP-hard, i.e. every NP language over every finite nonempty alphabet reduces to it in polynomial time.
--
--   So even computing a single optimal step of CTP on disjoint-path graphs is intractable unless P = NP, which is why Theorem 1 asks for an approximation.
--
--   **Formalization Note** The statement is unconditional; the NP-hardness of Subset Product, which the paper's proof cites, is not a hypothesis.
--
--   Differences from the source:
--   - encoding: the decision problem on explicitly given instances and a given edge → a language of strings over a 7-letter alphabet: binary codes of rational instances (value and probability as numerator/denominator pairs) plus an edge (i, j); non-codes and invalid lists are not in it; reason: the standard encoding of an explicit finite input; the reduction's instances (Definition 10) are rational
--   - encoding: NP-hard (no machine model named) → every language in CookPvsNP.NP over every finite nonempty alphabet is polynomial-time many-one reducible to it (published CookPvsNP_defs); reason: the standard notion of NP-hardness
--   - encoding: a policy traverses the edge as its first move → the edge is a first edge (j = 0) and, almost surely, whenever the second edge of some path is revealed the second edge of path i is (TraversesFirst); reason: on instances whose paths all have two edges the first traversal from s is exactly what reveals a second edge
--   - encoding: optimal adaptive policy (deterministic, history-dependent) → feasible randomized stateful policy with expCost = optCost (the published CanadaCTP.optCost); reason: the randomized stateful class contains the paper's policies and no mixture beats its best component, so the optimum and the optimal deterministic policies are the same
-- source:
--   Abels–Pitschmann–Schewior–Schmand, Canada Retravelled (manuscript, STOC 2027 submission, sha256 8117348eb78ba082edf376778214fa414f31cb0cd8a8d06c12a1dfba627e3a33), Theorem 6, p.26 (proof pp.27–28); Proposition 1, p.26

import Mathlib
import Definitions.Def_CanadaCTP_Supplement_FirstMove

namespace CanadaCTP.Supplement

/-- Abels–Pitschmann–Schewior–Schmand, *Canada Retravelled* (manuscript, sha256 8117348e…3a33),
Theorem 6, p.26 (proof pp.27–28): "Deciding whether there exists an optimal adaptive policy that
traverses a given edge as its first move in the Stochastic Canadian Traveller Problem is NP-hard
even on disjoint-path graphs, where every path has length 2 and for every path, the weight of the
first edge has a constant distribution and the weight of the second edge has a random distribution
with a support of size at most 3."

The language of codes of (instance, edge) queries in that class that admit an optimal adaptive
policy traversing the edge first is NP-hard: every NP language over every finite nonempty alphabet
reduces to it by a polynomial-time many-one reduction.

**Formalization Note.** The language is `firstMoveLang Thm6Class` (rational inputs, binary code,
non-codes and invalid lists rejected); NP and reductions are the published `CookPvsNP` ones. The
statement is unconditional: the NP-hardness of Subset Product used in the proof is not assumed. -/
theorem theorem_6 : NPHard (firstMoveLang Thm6Class) := by sorry

end CanadaCTP.Supplement
