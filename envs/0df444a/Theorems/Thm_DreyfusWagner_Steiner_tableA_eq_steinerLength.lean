-- Prove2me | Theorems.Thm_DreyfusWagner_Steiner_tableA_eq_steinerLength
-- name    : DreyfusWagner.Steiner.tableA_eq_steinerLength
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:07:11.834916+00:00
-- url     : https://prove2.me/theorems/26e716f6-8ea5-4254-a4f0-4ea4c1b80a47
-- title:
--   §2, p. 200 and §4, p. 203 — every table entry $S[D,I]$ of Algorithm A is the Steiner length of $\{I\} \cup D$
-- statement:
--   Let $G = (N, A)$ be a finite connected undirected graph whose arcs have positive lengths, with $N$ linearly ordered. Let $S[D, I]$ be the table of Algorithm A built from the shortest-path lengths $D(i,j)$ of $G$. Then for every nonempty node set $D$ and every node $I$,
--   $$S[D, I] = \operatorname{St}(\{I\} \cup D),$$
--   the length of the Steiner path $S(I, D)$ for the nodes $\{I\} \cup D$.
--
--   This is the invariant that the table of Algorithm A maintains: each entry is the optimal value of the subproblem it stands for. With it, the value returned by the algorithm is the recurrence of §2 evaluated at $m = q$ and $D = C$.
--
--   **Formalization Note** The statement is made for every nonempty $D$, not only for the proper subsets of $C = Y - \{q\}$ that the algorithm stores; the table is defined for all node sets by the same recursion.
-- source:
--   Dreyfus, Wagner, The Steiner Problem in Graphs, Networks 1 (1971), p. 200, §2 ('Let S(m,D) denote the Steiner path for nodes {m ∪ D}'), and p. 203, §4, Algorithm A, lines (1)–(14); worked values p. 201

import Mathlib
import Definitions.Def_DreyfusWagner_Steiner_SteinerProblem
import Definitions.Def_DreyfusWagner_Steiner_AlgorithmA

namespace DreyfusWagner.Steiner

/-- Dreyfus–Wagner 1971, §2, p. 200 and §4, p. 203: every entry `S[D, I]` of the table of
Algorithm A, built from the shortest-path lengths `D(i,j)`, is the length `S(I, D)` of the
Steiner path for the nodes `{I} ∪ D`. -/
theorem tableA_eq_steinerLength {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ)
    (hpos : ∀ e ∈ G.edgeSet, 0 < ℓ e) (hconn : G.Connected)
    (D : Finset V) (hD : D.Nonempty) (I : V) :
    tableA (pathDist G ℓ) D I = steinerLength G ℓ (insert I D) := by sorry

end DreyfusWagner.Steiner
