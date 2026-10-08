-- Prove2me | Theorems.Thm_ChinesePostman_NextNode_last_exit_unused_of_unused
-- name    : ChinesePostman.NextNode.last_exit_unused_of_unused
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:51:26.524973+00:00
-- url     : https://prove2.me/theorems/7d5548c9-a498-4867-beab-2786d109c0b2
-- title:
--   Proof of Theorem 5.1, p. 113 — at the stop, every node meeting an untraversed edge is not $r$ and its last exit $L_n(1)$ is unused
-- statement:
--   Let $G$, $r$ and $L$ be as in the previous step, with (i) and (ii). Follow the tour specified by the lists from $r$ until it stops, with $t_n$ departures made from each node $n$. Let $S$ be the set of nodes incident to untraversed edges: the nodes $n$ with an unused entry in $L_n$, together with the nodes $n$ that occur as an unused entry of some list $L_m$. Then for every $n \in S$
--
--   $$
--   n \ne r \quad\text{and}\quad L_n(1) \text{ is unused, i.e. } k_n - t_n \ge 1 .
--   $$
--
--   In words, for $n \in S$ the edge $(n, L_n(1))$ has not been traversed, since it is the last edge specified by the next-node list, and $r \notin S$.
--
--   Together with condition (iii) this yields the contradiction that closes the converse of Theorem 5.1.
--
--   **Formalization Note** The conclusion "$L_n(1)$ is unused" is stated as: the list $L_n$ is nonempty and its first entry is also the first entry of the unused part $L_n(1), \dots, L_n(k_n - t_n)$. Untraversed edges are expressed through unused list entries; by (ii), the edges between $n$ and $m$ correspond to the entries $m$ in $L_n$ and $n$ in $L_m$.
-- source:
--   Edmonds and Johnson, Matching, Euler tours and the Chinese postman, Math. Programming 5 (1973), p. 113, §5, proof of Theorem 5.1 (converse, the set S of nodes incident to untraversed edges)

import Mathlib
import Definitions.Def_ChinesePostman_NextNode_Setting

namespace ChinesePostman.NextNode

/-- Proof of Theorem 5.1, p. 113 (converse, second step): under (i) and (ii), when the traversal
from `r` stops, every node `n` incident to an untraversed edge (an unused entry of `L n`, or an
unused occurrence of `n` in some list `L m`) is different from `r`, and its last exit `L_n(1)` is
still unused. -/
theorem last_exit_unused_of_unused {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    (G : Graph V E) (r : V) (L : V → List V) (h1 : CondI G L) (h2 : CondII G L) (n : V)
    (hn : unused L (follow L r).2 n ≠ [] ∨ ∃ m, n ∈ unused L (follow L r).2 m) :
    n ≠ r ∧ ∃ m, (L n).head? = some m ∧ (unused L (follow L r).2 n).head? = some m := by sorry

end ChinesePostman.NextNode
