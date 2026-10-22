-- Prove2me | Theorems.Thm_DirS_dir_force_needs_cycle
-- name    : DirS.dir_force_needs_cycle
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-21T21:27:12.314421+00:00
-- url     : https://prove2.me/theorems/e7f2823b-66a5-42d9-8606-d1ccaed19ca4
-- title:
--   Directed forcing forces a homomorphism to the edge and an underlying cycle (Theorem 6)
-- statement:
--   Theorem 6 of the paper: if the oriented graph B has the directed forcing property, then B has a homomorphism to the directed edge K_2 and the underlying undirected graph of B contains a cycle. The edge half is Proposition 23 (the preceding milestone). For the cycle half, the paper observes that if the underlying graph is a forest, the density counts of B track a family that is not quasirandom - the reflected constructions of the concluding section - contradicting forcing. In the mission the conclusion is the conjunction of the homomorphism-to-edge property and the injective cyclic walk recorded by hasCycle.
--
--   **Formalization Note** The cycle is recorded as an injective cyclic sequence of vertices with undirected steps, which for a finite graph is equivalent to the paper's formulation through the containment of a cycle.
-- source:
--   J. Fox, Z. Himwich, N. Mani, Y. Zhou, A note on directed analogues of the Sidorenko and forcing conjectures, Electron. J. Combin. 32(3) (2025) #P3.38, Section 4 (Theorem 6, page 3, proved via Proposition 23 and the arguments of Section 4).

import Mathlib
import Definitions.Def_DirS_gr
import Definitions.Def_DirS_gw

namespace DirS

/-!  Milestone 6 (Theorem 6): directed forcing forces a homomorphism to
the edge and an underlying cycle. If the oriented graph B has the directed
forcing property, then B has a homomorphism to the directed edge K_2 and
the underlying undirected graph of B contains a cycle. The edge half is
Proposition 23 (milestone 5); the cycle half of the paper's proof
evaluates the forcing condition on the reflected-graph family - if the
underlying graph is a forest, the density counts track a non-quasirandom
family, contradicting forcing. -/
theorem dir_force_needs_cycle {m : ℕ} (B : OriGraph m) (h : DirForcing B) :
    homToEdge B ∧ hasCycle B := by sorry

end DirS
