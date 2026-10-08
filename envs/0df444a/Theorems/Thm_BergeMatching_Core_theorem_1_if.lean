-- Prove2me | Theorems.Thm_BergeMatching_Core_theorem_1_if
-- name    : BergeMatching.Core.theorem_1_if
-- status  : Proved
-- author  : @Tim
-- created : 2026-10-05T15:19:45.680058+00:00
-- url     : https://prove2.me/theorems/d34faa80-a261-4e9b-b13b-ef2d2f039730
-- title:
--   Berge (1957), Theorem 1, converse: a non-maximum matching has an alternating chain between two distinct neutral points
-- statement:
--   Let $G = (X, U)$ be a finite simple graph and $V \subseteq U$ a matching of $G$. Call the edges of $V$ strong and the other edges weak. A vertex met by no strong edge is **neutral**. An **alternating chain** is a walk that uses no edge twice and in which, of any two consecutive edges, one is strong and the other weak.
--
--   If $V$ is not a maximum matching, i.e. some matching of $G$ has more edges than $V$, then there exist neutral vertices $a \neq a'$ and an alternating chain connecting $a$ to $a'$:
--
--   $$
--   V \text{ not maximum} \;\Longrightarrow\; \exists\, a \neq a' \text{ neutral},\ \exists \text{ an alternating chain from } a \text{ to } a'.
--   $$
--
--   This is the converse half of Berge's characterization of maximum matchings: every non-maximum matching admits an augmenting chain. Together with the forward half (an augmenting chain enlarges the matching), it gives Theorem 1, and it is the correctness criterion behind augmenting-path matching algorithms.
--
--   **Formalization Note** Same conventions as `BergeMatching.Core.theorem_1`: the graph is a finite Mathlib `SimpleGraph`, the matching is a subgraph with `IsMatching`, and "maximum" compares edge counts (`ncard` of edge sets). Alternating chains are trails with alternation of consecutive edges. The endpoints are required to be distinct.
-- source:
--   Berge, Two theorems in graph theory, Proc. Natl. Acad. Sci. USA 43 (1957), pp. 842–844, p. 843, Theorem 1 (converse direction of the proof)

import Mathlib
import Definitions.Def_BergeMatching_Core_AlternatingChain

namespace BergeMatching.Core

/-- Berge (1957), p. 843, Theorem 1, converse ("if") direction: if a matching is not maximum,
then some alternating chain connects a neutral point to a different neutral point. -/
theorem theorem_1_if {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (M : G.Subgraph) (hM : M.IsMatching) (hnot : ¬ IsMaximumMatching M) :
    ∃ (a a' : V) (p : G.Walk a a'),
      a ≠ a' ∧ IsNeutral M a ∧ IsNeutral M a' ∧ IsAlternatingChain M p := by sorry

end BergeMatching.Core
