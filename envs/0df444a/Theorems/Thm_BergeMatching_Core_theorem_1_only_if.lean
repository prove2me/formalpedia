-- Prove2me | Theorems.Thm_BergeMatching_Core_theorem_1_only_if
-- name    : BergeMatching.Core.theorem_1_only_if
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:07:13.659031+00:00
-- url     : https://prove2.me/theorems/7fc5cb53-1054-4ae4-a7ae-14f2b826e164
-- title:
--   Proof of Theorem 1, first paragraph — an alternating chain between two neutral points augments the matching
-- statement:
--   Let $G = (X, U)$ be a finite simple graph and $V \subseteq U$ a matching, with neutral points $N$ (vertices met by no edge of $V$). Suppose $W$ is an alternating chain (a walk that uses no edge twice and whose consecutive edges alternate between edges of $V$ and edges not in $V$) connecting a neutral point $a$ to a neutral point $a' \neq a$. Then the symmetric difference
--   $$
--   V' = (V \setminus W) \cup (W \setminus V)
--   $$
--   is a matching of $G$ with $|V'| > |V|$; in particular $V$ is not a maximum matching.
--
--   This is the "only if" half of Theorem 1: an alternating chain joining two distinct neutral points is an augmenting chain.
--
--   **Formalization Note** $W$ is identified with the set of edges of the walk. The conclusion asserts the existence of a matching subgraph whose edge set is exactly this symmetric difference, that it has strictly more edges, and that the original matching is not maximum.
-- source:
--   Berge, Two theorems in graph theory, Proc. Natl. Acad. Sci. USA 43 (1957), p. 843, proof of Theorem 1, first paragraph

import Mathlib
import Definitions.Def_BergeMatching_Core_AlternatingChain

namespace BergeMatching.Core

/-- Berge (1957), p. 843, proof of Theorem 1, first paragraph: if an alternating chain `W`
connects a neutral point `a` to a neutral point `a' ≠ a`, then `(V - W) ∪ (W - V)` is a matching
with more elements than `V`, and `V` is not maximum. -/
theorem theorem_1_only_if {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (M : G.Subgraph) (hM : M.IsMatching) {a a' : V} (p : G.Walk a a')
    (haa' : a ≠ a') (ha : IsNeutral M a) (ha' : IsNeutral M a') (hp : IsAlternatingChain M p) :
    ∃ M' : G.Subgraph, M'.IsMatching ∧
      M'.edgeSet = symmDiff M.edgeSet {e | e ∈ p.edges} ∧
      M.edgeSet.ncard < M'.edgeSet.ncard ∧ ¬ IsMaximumMatching M := by sorry

end BergeMatching.Core
