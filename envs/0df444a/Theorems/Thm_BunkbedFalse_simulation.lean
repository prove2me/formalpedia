-- Prove2me | Theorems.Thm_BunkbedFalse_simulation
-- name    : BunkbedFalse.simulation
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-12T13:16:09.180199+00:00
-- url     : https://prove2.me/theorems/da00ff93-1600-4f63-9931-a75ab8a2fe42
-- title:
--   The substituted graph simulates the Wierman--Ziff model
-- statement:
--   This is the bridge between Sections 3 and 4 of Gladkov--Pak--Zimin: the statement that substituting a gadget for each hyperedge turns bunkbed percolation on an honest *graph* into the Wierman--Ziff model on a *hypergraph*.
--
--   Let $G$ be the graph obtained from Hollom's hypergraph by substituting a copy of the gadget $G_{1204}$ for each of its six $3$-hyperedges — apex identified with the transversal vertex, path ends with the other two vertices, interior fresh. Then for all hypergraph vertices $x, y$ and each level $l$,
--
--   $$\mathbb{P}^{\mathrm{bb}}_{1/2}\bigl[(x,0) \leftrightarrow (y,l)\bigr] \;=\; \mathbb{P}^{\mathrm{wz}}_{P}\bigl[(x,0) \leftrightarrow (y,l)\bigr],$$
--
--   where on the right the Wierman--Ziff state distribution $P$ assigns to each of the five states the corresponding partition probability of the gadget under $\tfrac12$-percolation.
--
--   **Why it is true.** Three facts combine.
--
--   *Independence.* The six gadget copies are edge-disjoint, so percolation on their union is the product of the percolations on the copies: the sum defining $\mathbb{P}^{\mathrm{bb}}$ becomes a sum over tuples of per-copy configurations, one tuple per level, weighted by products of per-copy weights.
--
--   *Only the boundary partitions matter.* Both graphs are unions of parts meeting only along the lifted hypergraph vertices. A copy's interior vertices are private to it, and a Wierman--Ziff state's canonical edge set has no interior vertices at all. So connectivity between hypergraph vertices depends only on the partition each part induces on them — and a state's canonical edges realise exactly the partition the state names.
--
--   *The copies behave as the gadget.* Each copy is an injective image of $G_{1204}$, reachability transports along an injective relabelling, and at $P = 1/2$ the gadget's weight function is the constant $1/2$, so the weights transport trivially. Hence each copy's five partition probabilities are the gadget's.
--
--   Grouping the tuple sum by the state tuple that the configurations induce, and factorising the weights over the copies, turns the left-hand side into the right.
--
--   **Mathematical role.** This is what makes the whole strategy work. Hollom refuted the $3$-uniform *hypergraph* bunkbed conjecture, and it is impossible to simulate a $3$-hyperedge exactly by bond percolation on any graph. The robustness lemma says the refutation nevertheless survives an approximate simulation, provided the simulating object's partition probabilities satisfy a quantitative condition; this theorem is the statement that the gadget-substituted graph *is* such a simulation, exactly, as a Wierman--Ziff model. Combined with the verification that the gadget meets the condition, it yields Theorem 1.2.
-- source:
--   N. Gladkov, I. Pak, A. Zimin, The bunkbed conjecture is false, PNAS 122 (2025) no. 24, e2420725122, https://doi.org/10.1073/pnas.2420725122, Section 4 (pp. 6-7): hyperedge simulation and the proof of Theorem 1.2.

import Definitions.Def_BunkbedSubstituted
open Bunkbed Bunkbed.Hyper Finset SimpleGraph

namespace BunkbedFalse

/-- **The substituted graph simulates the Wierman-Ziff model.** Bunkbed percolation at `1/2` on
the graph obtained by substituting a copy of `G₁₂₀₄` for each hyperedge of Hollom's hypergraph is
*exactly* the Wierman-Ziff model on that hypergraph, with the gadget's five partition
probabilities as the state distribution. -/
theorem simulation (x y : Fin 10) (l : Fin 2) :
    bbProb Bunkbed.Sub.subEdges (fun _ => (1 / 2 : ℚ)) Bunkbed.Sub.subT
        (Bunkbed.Sub.iota x, 0) (Bunkbed.Sub.iota y, l)
      = wzProb hollomTriple hollomT
          (fun s => match s with
            | WZ.abc   => Pabc   (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
            | WZ.a_b_c => Pa_b_c (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
            | WZ.a_bc  => Pa_bc  (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
            | WZ.ab_c  => Pab_c  (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204)
            | WZ.ac_b  => Pac_b  (gadgetE 1204) (gadgetW 1204 (1 / 2)) 0 1 (Fin.last 1204))
          (x, 0) (y, l) := by
  sorry

end BunkbedFalse
