-- Prove2me | Theorems.Thm_BunkbedFalse_sub_invariants
-- name    : BunkbedFalse.sub_invariants
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T04:22:46.79438+00:00
-- url     : https://prove2.me/theorems/cea1b221-ae02-4554-8ed4-5c3896fa1822
-- title:
--   The substituted graph has 14442 edges, three transversal vertices, and is connected
-- statement:
--   Theorem 1.2 of Gladkov--Pak--Zimin asserts the existence of a connected graph on $7{,}222$ vertices with $14{,}442$ edges and a transversal set of size three, on which bunkbed percolation at $P = 1/2$ violates the conjecture. This theorem establishes the three combinatorial assertions for the explicit graph constructed by substituting a copy of the gadget $G_{1204}$ for each of the six hyperedges of Hollom's hypergraph.
--
--   1. **Edge count.** $|E| = 14{,}442$. The six embedded copies are pairwise disjoint, each copy is an injective image of $G_{1204}$, and $G_n$ has $2n-1$ edges, so the total is $6 \cdot 2407 = 14{,}442$. Since no embedded edge is a loop, the number of edges of the *graph* agrees with the cardinality of the edge set.
--
--   2. **Transversal set.** $|T| = 3$, being the injective image of $\texttt{hollomT} = \{u_2, u_7, u_9\}$. Three is the smallest number of transversal vertices for which the bunkbed conjecture can fail.
--
--   3. **Connectivity.** Each gadget copy is connected, because its apex is adjacent to every one of its path vertices. The copies are then glued along the path $u_1, u_3, u_6, u_5, u_4, u_8, u_{10}$: copy $i$ contains both the $i$-th and the $(i+1)$-st vertex of that path. So every vertex reaches $u_1$ — first by moving inside its own copy to that copy's apex or path end, then by walking down the chain of copies.
--
--   **Mathematical role.** Together with the identification of bunkbed percolation on this graph as a Wierman--Ziff model on Hollom's hypergraph, and the verification that the gadget's partition probabilities satisfy the conditions of the robustness lemma, these three facts complete Theorem 1.2. Note that the published Theorem 1.2 also asserts planarity; that cannot presently be stated, as Mathlib has no notion of a planar graph, so the formalised statement is weaker in that respect.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Theorem 1.2 (p. 1) and Section 4.2 (p. 7).

import Definitions.Def_BunkbedSubstituted
open Bunkbed Bunkbed.Hyper Finset SimpleGraph

namespace BunkbedFalse

/-- **The invariants of the substituted graph.** It has 14442 edges, its transversal set has three
vertices, and it is connected. -/
theorem sub_invariants :
    (ofEdges Bunkbed.Sub.subEdges).edgeFinset.card = 14442 ∧ Bunkbed.Sub.subT.card = 3
      ∧ (ofEdges Bunkbed.Sub.subEdges).Connected := by
  sorry

end BunkbedFalse
