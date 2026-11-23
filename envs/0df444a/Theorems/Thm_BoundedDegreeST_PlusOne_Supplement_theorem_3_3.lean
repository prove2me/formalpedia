-- Prove2me | Theorems.Thm_BoundedDegreeST_PlusOne_Supplement_theorem_3_3
-- name    : BoundedDegreeST.PlusOne.Supplement.theorem_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:49:31.251959+00:00
-- url     : https://prove2.me/theorems/e89ec3a2-c7ba-4fdd-8199-29877ada584d
-- title:
--   Theorem 3.3 — polynomial-time (1, B_v+2) approximation (corrected: final singleton convention)
-- statement:
--   Let $G=(V,E)$ be a finite simple undirected graph, with arbitrary real edge costs $c_e$ and integer degree bounds $B_v$. Assume its degree-constrained spanning-tree LP is feasible. The leaf-deletion algorithm of Figure 2 has a finite run; every run prefix has at most $2|V|-1$ iterations. Every returned edge set $H$ is a spanning tree on all the original vertices, is contained in $E$, and satisfies
--
--   $$d_H(v)\le B_v+2\quad(v\in V),\qquad c(H)\le\sum_{e\in E}c_ex_e\quad\text{for every LP-feasible }x.$$
--
--   Consequently $c(H)\le c(T)$ for every spanning tree $T\subseteq E$ satisfying the original bounds, including an optimum whenever it exists. The statement includes all choices of basic optimal vectors, leaves and eligible constraints.
--
--   For rational costs encoded in binary, there exist two uniform deterministic polynomial-time Turing-machine implementations: one finds an exact basic optimal vector for every feasible residual LP, and the other returns a Figure 2 output for every feasible original instance. Their polynomial clocks are measured in the full binary input length, including the signed bounds and cost numerators and denominators. The LP solver is a conclusion, not a free oracle premise. The real-cost correctness clause has no sign or rationality assumption.
--
--   This is the companion $B_v+2$ theorem from §3, attributed there to Goemans. The published mission's immutable $B_v+1$ goal is reused separately; this theorem does not serve as a step in its proof.
--
--   Differences from the source:
--   - generalization: an algorithm for instances with an original degree-feasible spanning tree → Figure 2 succeeds on every LP-feasible instance and every returned tree costs no more than any feasible LP vector; reason: the p. 664 argument preserves the LP objective and requires only LP feasibility; every original feasible tree supplies an LP benchmark
--   - reading: the algorithm returns and takes at most 2n−1 iterations → a run exists, every nonterminal run prefix has length at most 2n−1, and every output has the guarantee; reason: makes termination and arbitrary source choices explicit and excludes a stuck return relation
--   - encoding: polynomial time, with a polynomial-time LP implementation described on p. 664 → one uniform polynomial-time binary Turing machine solves every feasible rational residual LP and another computes a Figure 2 output; correctness still holds for arbitrary real costs; reason: finite input encodings give the standard bit-complexity assertion, including the LP computation rather than charging it as a free oracle
--   - correction: Figure 2 loops while the residual vertex set is nonempty and its Step 2b tests "at most one edge", referring to a leaf edge even at degree zero → stop when at most one residual vertex remains, add no edge for the final isolated vertex, and test support degree exactly one in Step 2b; reason: the leaf explanation on p. 664 explicitly uses degree one; a feasible singleton has zero total LP mass and no edge; no feasible input is excluded
--   - encoding: finite simple graphs and the spanning-tree LP with vertexwise bounds → unordered non-diagonal edges, surviving-vertex subtypes, integer residual bounds, and nonempty subtour sets in the published LP; reason: preserves the graph and update domains and removes the unintended impossible empty-set row
-- source:
--   Singh, Lau, Approximating minimum bounded degree spanning trees to within one of optimal, STOC 2007, DOI 10.1145/1250790.1250887, p. 665, Theorem 3.3; p. 664, Figure 2, Eqs. (10)–(14), LP implementation paragraph and iteration count

import Definitions.Def_BoundedDegreeST_PlusOne_Supplement_Computation

namespace BoundedDegreeST.PlusOne.Supplement

/-- Theorem 3.3, STOC 2007 p. 665. The actual LP implementation and the
Figure 2 implementation have uniform polynomial Turing-machine clocks on
binary rational inputs. Real-cost correctness and the iteration bound retain
the full mathematical domain, without a rationality or sign hypothesis. -/
theorem theorem_3_3 :
    FigureTwoCorrect ∧
    ∃ solve run : List Bool → List Bool,
      Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
        (id : List Bool → List Bool) solve) ∧
      ImplementsLP solve ∧
      Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
        (id : List Bool → List Bool) run) ∧
      ImplementsFigureTwo run := by sorry

end BoundedDegreeST.PlusOne.Supplement
