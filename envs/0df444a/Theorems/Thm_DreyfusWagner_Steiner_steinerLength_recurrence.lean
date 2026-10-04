-- Prove2me | Theorems.Thm_DreyfusWagner_Steiner_steinerLength_recurrence
-- name    : DreyfusWagner.Steiner.steinerLength_recurrence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:06:33.356905+00:00
-- url     : https://prove2.me/theorems/137029f2-1858-4816-a11d-97f93e9517e9
-- title:
--   §2, pp. 199–200 — the recurrence $S(m,D) = \min_k (d_{mk} + S_k(D))$
-- statement:
--   Let $G = (N, A)$ be a finite connected undirected graph whose arcs have positive lengths, let $d_{mk} = D(m,k)$ be the shortest-path length from $m$ to $k$, and let $\operatorname{St}(X)$ be the Steiner length of a node set $X$. Let $D \subseteq N$ have at least two nodes and let $m \in N$ be any node. For $k \in N$ put
--   $$S_k(D) = \min\big\{\operatorname{St}(\{k\} \cup E) + \operatorname{St}(\{k\} \cup (D - E)) : \emptyset \ne E \subsetneq D\big\},$$
--   the best way of joining the two parts of a splitting of $D$ into nonempty disjoint sets $E$, $F = D - E$ at the node $k$. Then
--   $$\operatorname{St}(\{m\} \cup D) = \min_{k \in N}\big(d_{mk} + S_k(D)\big).$$
--
--   This is the dynamic-programming recurrence of Dreyfus and Wagner: the Steiner length for a terminal set of size $j+1$ is obtained from shortest-path lengths and Steiner lengths of terminal sets of size at most $j$. The node $m$ may belong to $D$.
-- source:
--   Dreyfus, Wagner, The Steiner Problem in Graphs, Networks 1 (1971), pp. 199–200, §2, last paragraph of p. 199 continued on p. 200 (definition of S_k(D), d_mk and S(m,D))

import Mathlib
import Definitions.Def_DreyfusWagner_Steiner_SteinerProblem

namespace DreyfusWagner.Steiner

/-- Dreyfus–Wagner 1971, §2, pp. 199–200: for a set `D` of at least two nodes and any node `m`,
the Steiner length of `{m} ∪ D` is `min_k (d_mk + S_k(D))`, where
`S_k(D)` is the minimum, over all splittings of `D` into two nonempty disjoint parts `E` and
`F = D − E`, of the Steiner lengths of `{k} ∪ E` and `{k} ∪ F` added together. -/
theorem steinerLength_recurrence {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ)
    (hpos : ∀ e ∈ G.edgeSet, 0 < ℓ e) (hconn : G.Connected)
    (D : Finset V) (hD : 2 ≤ D.card) (m : V) :
    steinerLength G ℓ (insert m D) =
      Finset.univ.inf fun k => pathDist G ℓ m k +
        (D.powerset.filter fun E => E.Nonempty ∧ E ≠ D).inf fun E =>
          steinerLength G ℓ (insert k E) + steinerLength G ℓ (insert k (D \ E)) := by sorry

end DreyfusWagner.Steiner
