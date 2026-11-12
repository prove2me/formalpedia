-- Prove2me | Theorems.Thm_BunkbedAux_gadgetE_card
-- name    : BunkbedAux.gadgetE_card
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T04:07:22.859804+00:00
-- url     : https://prove2.me/theorems/0e6cec00-d356-4d5f-bf55-bf96aa90b707
-- title:
--   The gadget $G_n$ has $2n-1$ edges
-- statement:
--   The gadget $G_n$ of Gladkov--Pak--Zimin (Figure 2) has vertex set $\{0, 1, \dots, n\}$ and consists of a path $v_1 - v_2 - \cdots - v_n$ on the vertices $1, \dots, n$, together with a hub $a = 0$ joined to every path vertex. It is the graph used to simulate a $3$-hyperedge, with the three distinguished vertices being the hub and the two ends of the path.
--
--   This theorem counts its edges:
--   $$|E(G_n)| \;=\; 2n - 1,$$
--   namely the $n$ **spokes** $\{0, v_j\}$ for $1 \le j \le n$, plus the $n - 1$ **path edges** $\{v_i, v_{i+1}\}$ for $1 \le i \le n-1$.
--
--   The proof splits the edge set into those two families, shows each has the stated size, and shows they are disjoint — a spoke is incident to the hub and a path edge is not.
--
--   **Mathematical role.** This is the combinatorial input to the edge count of the counterexample graph of Theorem 1.2. That graph substitutes a copy of $G_{1204}$ for each of the six hyperedges of Hollom's hypergraph, and the six copies are edge-disjoint, so its edge count is
--   $$6 \cdot (2 \cdot 1204 - 1) \;=\; 6 \cdot 2407 \;=\; 14{,}442,$$
--   which is the figure appearing in the statement of Theorem 1.2.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Figure 2 (p. 6) and Section 4.2 (p. 7), where the edge count 6*2407 = 14442 of the counterexample graph is stated.

import Definitions.Def_BunkbedPercolation
open Bunkbed SimpleGraph Finset

namespace BunkbedAux

/-- **The gadget `Gₙ` has `2n - 1` edges**: `n` spokes from the apex to each path vertex, and
`n - 1` path edges. -/
theorem gadgetE_card (n : ℕ) : (gadgetE n).card = 2 * n - 1 := by
  sorry

end BunkbedAux
