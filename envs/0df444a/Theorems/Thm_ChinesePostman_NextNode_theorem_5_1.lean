-- Prove2me | Theorems.Thm_ChinesePostman_NextNode_theorem_5_1
-- name    : ChinesePostman.NextNode.theorem_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:51:16.442382+00:00
-- url     : https://prove2.me/theorems/f83c384c-55a8-4b03-bcab-41a4399bde33
-- title:
--   Theorem 5.1, p. 112 — next-node lists describe an Euler tour iff (i) $k_n = \deg(n)/2$, (ii) edge counts match, (iii) the last-exit edges form an arborescence
-- statement:
--   Let $r$ be any node of an even, connected, finite loopless multigraph $G$, and let $L_n(1), \dots, L_n(k_n)$ be next-node lists for $G$. The lists describe an Euler tour (the tour specified by the lists from $r$ uses every list entry and is an Euler tour of $G$) if and only if all of the following hold:
--
--   1. (i) for every node $n$, the length $k_n$ of the list of $n$ equals one half of the degree of $n$;
--   2. (ii) for all nodes $n, m$, the number of edges meeting both $n$ and $m$ equals the number of $i$ with $n = L_m(i)$ plus the number of $i$ with $m = L_n(i)$;
--   3. (iii) the edges $(n, L_n(1))$, $n \ne r$, directed from $n$ to $L_n(1)$, form an arborescence with root $r$.
--
--   $$
--   L \text{ describes an Euler tour from } r \iff \text{(i)} \wedge \text{(ii)} \wedge \text{(iii)} .
--   $$
--
--   An arborescence with root $r$ is a tree with a direction on each edge such that every node $n \ne r$ has exactly one edge directed away from it and $r$ has none.
--
--   The theorem certifies the next-node representation of Euler tours: three local, easily checked conditions on the lists guarantee that following them from $r$ traverses every edge exactly once. Theorem 5.2 shows that the next-node algorithm produces lists with these properties.
--
--   **Formalization Note** The printed condition (iii) names the edges $(n, L_n(k_n))$, the first exits; the paper's proofs of Theorems 5.1 and 5.2 use $(n, L_n(1))$, the last exits, and the printed version is false (the graph with edges $r$–$a$, $a$–$c$, $a$–$c$, $a$–$b$, $b$–$r$ and the tour $r, a, c, a, b, r$ has first exits $a \to c \to a$ forming a cycle). The statement uses $L_n(1)$. The lists are read backwards: the first departure from $n$ goes to $L_n(k_n)$; reading them forwards would be a different theorem. (iii) requires every node $n \ne r$ to have a nonempty list. A graph with one node and no edges is allowed: all lists are empty, the one-node tour is an Euler tour, and both sides hold.
-- source:
--   Edmonds and Johnson, Matching, Euler tours and the Chinese postman, Math. Programming 5 (1973), p. 112, Theorem 5.1 (with the definition of an arborescence on p. 112 and the next-node representation on p. 109)

import Mathlib
import Definitions.Def_ChinesePostman_NextNode_Setting

namespace ChinesePostman.NextNode

/-- Theorem 5.1, p. 112: for any node `r` of an even, connected graph `G`, next-node lists describe
an Euler tour (from `r`) if and only if (i), (ii) and (iii) hold, with (iii) for the edges
`(n, L_n(1))`, `n ≠ r`. -/
theorem theorem_5_1 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E) (hconn : Connected G) (heven : ∀ n, Even (degree G n)) (r : V)
    (L : V → List V) :
    DescribesEulerTour G r L ↔ CondI G L ∧ CondII G L ∧ CondIII G r L := by sorry

end ChinesePostman.NextNode
