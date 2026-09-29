-- Prove2me | Theorems.Thm_DreyfusWagner_Steiner_algorithmA_eq_steinerLength
-- name    : DreyfusWagner.Steiner.algorithmA_eq_steinerLength
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T12:08:42.566319+00:00
-- url     : https://prove2.me/theorems/beeff2e1-47fd-4fed-8cb9-15b76b4e2909
-- title:
--   Algorithm A computes the length of the Steiner tree connecting $Y$
-- statement:
--   Let $G = (N, A)$ be a finite connected undirected graph whose arcs have positive lengths, with the node set $N$ linearly ordered in any way. Let $Y \subseteq N$ contain at least three nodes and let $q \in Y$. Then the value $v$ returned by Algorithm A of Dreyfus and Wagner (with $C = Y - \{q\}$ and the shortest-path lengths $D(i,j)$ of $G$ as input) is the length of the Steiner tree connecting $Y$:
--   $$v = \operatorname{St}(Y) = \min\{\, |S| : S \subseteq A,\ S \text{ connects } Y \,\}.$$
--
--   This is the main result of the paper: the Dreyfus–Wagner dynamic program solves the Steiner problem in graphs exactly, in time exponential only in the number of terminals.
--
--   **Formalization Note** The hypothesis $\|Y\| \ge 3$ is the paper's own (Appendix A, p. 205). For $\|Y\| = 2$ Algorithm A as printed returns $+\infty$ (line (18) admits no set $E$), and the two-node case is covered by the shortest path instead. The order on $N$ is arbitrary: the conclusion holds for every choice of $A[1]$. Values are in `WithTop ℝ`; under the hypotheses both sides are finite.
-- source:
--   Dreyfus, Wagner, The Steiner Problem in Graphs, Networks 1 (1971), p. 203, §4, Algorithm A (caption: 'Computes the length of the Steiner tree connecting Y'); Abstract, p. 195; hypothesis ‖Y‖ ≥ 3 from Appendix A, p. 205

import Mathlib
import Definitions.Def_DreyfusWagner_Steiner_SteinerProblem
import Definitions.Def_DreyfusWagner_Steiner_AlgorithmA

namespace DreyfusWagner.Steiner

/-- Dreyfus–Wagner 1971, §4, Algorithm A, p. 203: for a finite connected undirected graph with
positive arc lengths, a set `Y` of at least three nodes and any `q ∈ Y`, Algorithm A returns
the length of the Steiner tree connecting `Y`, whatever the order of the nodes. -/
theorem algorithmA_eq_steinerLength {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (ℓ : Sym2 V → ℝ)
    (hpos : ∀ e ∈ G.edgeSet, 0 < ℓ e) (hconn : G.Connected)
    (Y : Finset V) (hY : 3 ≤ Y.card) (q : V) (hq : q ∈ Y) :
    algorithmA G ℓ Y q = steinerLength G ℓ Y := by sorry

end DreyfusWagner.Steiner
