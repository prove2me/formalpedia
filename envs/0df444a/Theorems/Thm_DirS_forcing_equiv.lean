-- Prove2me | Theorems.Thm_DirS_forcing_equiv
-- name    : DirS.forcing_equiv
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-21T21:27:48.852805+00:00
-- url     : https://prove2.me/theorems/671434d2-a465-4c69-8927-79d3bdd78e96
-- title:
--   Directed and asymmetric forcing are equivalent (Theorem 8)
-- statement:
--   Theorem 8 of the paper: let B be an oriented graph with a homomorphism to the directed edge K_2. Then the underlying undirected graph of B has the asymmetric forcing property if and only if B has the directed forcing property. The statement here is taken with B the orientation of a bipartite graph H, which has a homomorphism to the edge automatically, so the hypothesis is discharged by the presentation. The two directions of the proof pass near-quasirandom sequences from one side to the other: a bipartite sequence is halved into a directed sequence through the graphon approximation (the kernel W/2 of the paper), and a directed sequence is read as a bipartite sequence through Observation 16 and Theorem 13; the counting Lemma 18 controls the errors.
--
--   **Formalization Note** The halving and doubling of the kernels is carried by the graph world's approximation data; the finitary epsilon-delta form of both forcing properties makes the epsilons and deltas compose without sequences.
-- source:
--   J. Fox, Z. Himwich, N. Mani, Y. Zhou, A note on directed analogues of the Sidorenko and forcing conjectures, Electron. J. Combin. 32(3) (2025) #P3.38, Section 4 (Theorem 8, page 4, proved on pages 11-12).

import Mathlib
import Definitions.Def_DirS_gr
import Definitions.Def_DirS_gw

namespace DirS

/-!  Milestone 7 (Theorem 8): directed and asymmetric forcing are
equivalent. For every bipartite graph H, the asymmetric forcing property
of H and the directed forcing property of the orientation of H are
equivalent. The orientation of H has a homomorphism to the edge
automatically, so the hypothesis of Theorem 8 of the paper is satisfied;
the two directions of the proof pass a near-quasirandom sequence on one
side to the other through the graphon approximation scheme of the world,
halving the bipartite kernel on the directed side. -/
theorem forcing_equiv (m n : ℕ) (H : BipGraph m n) :
    AsymForcing H ↔ DirForcing (orientOf H) := by sorry

end DirS
