-- Prove2me | Theorems.Thm_ChinesePostman_NextNode_exists_last_exit_leaving
-- name    : ChinesePostman.NextNode.exists_last_exit_leaving
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:51:03.712057+00:00
-- url     : https://prove2.me/theorems/7df9dc91-cb58-420e-8a62-3cc4713b2b31
-- title:
--   Proof of Theorem 5.1, p. 113 — the last-exit edges leave every node set not containing $r$
-- statement:
--   Let $G$ be a connected finite loopless multigraph, $r$ a node and $L$ next-node lists that describe an Euler tour from $r$. Then every node $n \ne r$ has a nonempty list, so its last exit $L_n(1)$ exists, and for every nonempty set $S$ of nodes with $r \notin S$
--
--   $$
--   \exists\, n \in S:\quad L_n(1) \notin S .
--   $$
--
--   In words: the collection $T$ of directed edges $n \to L_n(1)$, $n \ne r$, has exactly one edge leaving each $n \ne r$ and has an edge leaving every node set that avoids $r$, since otherwise the tour, once it reaches $S$, would stay in $S$.
--
--   This is the cut property from which the paper concludes that $T$ is an arborescence (condition (iii) of Theorem 5.1).
--
--   **Formalization Note** The page writes the edges as $(n, L_n(k_n))$; the argument ("the Euler tour would eventually reach $S$ and stay in $S$") holds for the last exits $L_n(1)$ and fails for the first exits $L_n(k_n)$, and the paper's converse proof uses $L_n(1)$. The statement uses $L_n(1)$, the head of the list. Connectivity is used for the nonemptiness of the lists of nodes $n \ne r$; even degrees are not needed.
-- source:
--   Edmonds and Johnson, Matching, Euler tours and the Chinese postman, Math. Programming 5 (1973), p. 113, §5, proof of Theorem 5.1 (necessity of (iii))

import Mathlib
import Definitions.Def_ChinesePostman_NextNode_Setting

namespace ChinesePostman.NextNode

/-- Proof of Theorem 5.1, p. 113 (necessity of (iii)): if next-node lists describe an Euler tour of
a connected graph, then every node `n ≠ r` has a last exit `L_n(1)`, and every nonempty set `S` of
nodes not containing `r` has a node `n ∈ S` whose last exit `L_n(1)` lies outside `S`. -/
theorem exists_last_exit_leaving {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : Graph V E) (hconn : Connected G) (r : V) (L : V → List V)
    (h : DescribesEulerTour G r L) :
    (∀ n, n ≠ r → L n ≠ []) ∧
      ∀ S : Finset V, S.Nonempty → r ∉ S →
        ∃ n ∈ S, ∃ m, (L n).head? = some m ∧ m ∉ S := by sorry

end ChinesePostman.NextNode
