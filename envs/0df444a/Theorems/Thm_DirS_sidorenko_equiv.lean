-- Prove2me | Theorems.Thm_DirS_sidorenko_equiv
-- name    : DirS.sidorenko_equiv
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-21T21:31:27.850196+00:00
-- url     : https://prove2.me/theorems/5f9a1085-d701-415a-a915-c7c618214180
-- title:
--   Directed and asymmetric Sidorenko are equivalent (Theorem 5)
-- statement:
--   Theorem 5 of the paper, the main equivalence: if B is an oriented graph with a homomorphism to K_2, then the underlying undirected bipartite graph of B has the asymmetric Sidorenko property if and only if B has the directed Sidorenko property. The statement here is taken with B the orientation of a bipartite graph H, so the homomorphism-to-edge hypothesis is discharged by the presentation. The proof composes the graphon characterizations: by Proposition 22, asymmetric Sidorenko for the underlying graph is the graphon inequality t_bip >= |E W|^{e}; by Observation 16 the bipartite density of the graph is the directed density of its orientation; and by Proposition 21 the directed Sidorenko property is the very same graphon inequality. The conjectural converse directions of the paper - Conjecture 4 and Conjecture 7 - remain open and are deliberately not formalized.
--
--   **Formalization Note** The equivalence of the two Sidorenko properties is the goal of the mission; the equivalence of the two forcing properties (the preceding milestone) is its forcing counterpart. The quantifier shapes match on the two sides because the orientation presentation fixes the parts.
-- source:
--   J. Fox, Z. Himwich, N. Mani, Y. Zhou, A note on directed analogues of the Sidorenko and forcing conjectures, Electron. J. Combin. 32(3) (2025) #P3.38, Section 3 (Theorem 5, page 3, proved on pages 9-10 via Observation 16 and Propositions 21 and 22).

import Mathlib
import Definitions.Def_DirS_gr
import Definitions.Def_DirS_gw

namespace DirS

/-!  The goal (Theorem 5): directed and asymmetric Sidorenko are
equivalent. For every bipartite graph H, the asymmetric Sidorenko property
of H and the directed Sidorenko property of the orientation of H are
equivalent. The proof runs through the graphon characterizations of
Propositions 21 and 22 (milestones 2 and 3) and the density agreement of
Observation 16 (milestone 1): the bipartite density of H in a graphon is
the directed density of its orientation in the same graphon, and the
exponents agree, so the two graphon inequalities coincide. The
conjectural converse directions of the paper - Conjecture 4, that every
bipartite oriented graph with a homomorphism to the edge has the directed
Sidorenko property, and Conjecture 7, its forcing counterpart - remain
open and are deliberately not formalized. -/
theorem sidorenko_equiv (m n : ℕ) (H : BipGraph m n) :
    AsymSidorenko H ↔ DirSidorenko (orientOf H) := by sorry

end DirS
