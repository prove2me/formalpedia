-- Prove2me | Theorems.Thm_ChinesePostman_NextNode_reaches_root_of_cut_property
-- name    : ChinesePostman.NextNode.reaches_root_of_cut_property
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:51:13.953009+00:00
-- url     : https://prove2.me/theorems/76092f32-b5c3-4e0b-a86b-8bdbd697d425
-- title:
--   Proof of Theorem 5.1, p. 113 — one out-edge per node $n \ne r$ and an edge leaving every set avoiding $r$ give an arborescence
-- statement:
--   Let $V$ be a finite set, $r \in V$ and $p : V \to V$ a map, read as the directed edges $n \to p(n)$ for $n \ne r$. Suppose every nonempty $S \subseteq V$ with $r \notin S$ contains a node $n$ with $p(n) \notin S$. Let $q(u) = r$ if $u = r$ and $q(u) = p(u)$ otherwise. Then
--
--   $$
--   \forall\, n \in V\ \ \exists\, j \ge 0:\quad q^{j}(n) = r .
--   $$
--
--   So the edges $n \to p(n)$, $n \ne r$, form a connected graph on all of $V$ with one fewer edge than nodes, that is a tree, directed towards $r$: an arborescence with root $r$.
--
--   This purely combinatorial step turns the cut property of the last-exit edges into condition (iii) of Theorem 5.1.
--
--   **Formalization Note** "The edges form an arborescence with root $r$" is expressed by: iterating $q$ from any node reaches $r$. With exactly one outgoing edge at each $n \ne r$ and none at $r$, this is equivalent to $T$ being a spanning tree directed to $r$.
-- source:
--   Edmonds and Johnson, Matching, Euler tours and the Chinese postman, Math. Programming 5 (1973), p. 113, §5, proof of Theorem 5.1 ("Therefore, T must form a connected graph including every node of G … Hence, (iii) is true.")

import Mathlib
import Definitions.Def_ChinesePostman_NextNode_Setting

namespace ChinesePostman.NextNode

/-- Proof of Theorem 5.1, p. 113: a map `p` giving each node `n ≠ r` one outgoing edge
`n → p n`, such that every nonempty node set `S` with `r ∉ S` has an edge leaving `S`, forms an
arborescence with root `r`: iterating `n ↦ p n` (with `r` fixed) leads every node to `r`. -/
theorem reaches_root_of_cut_property {V : Type} [Fintype V] [DecidableEq V] (p : V → V) (r : V)
    (h : ∀ S : Finset V, S.Nonempty → r ∉ S → ∃ n ∈ S, p n ∉ S) :
    ∀ n, ∃ j : ℕ, (fun u => if u = r then r else p u)^[j] n = r := by sorry

end ChinesePostman.NextNode
