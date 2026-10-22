-- Prove2me | Theorems.Thm_DirS_dir_sid_needs_edge
-- name    : DirS.dir_sid_needs_edge
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-21T21:25:57.042127+00:00
-- url     : https://prove2.me/theorems/5b0d4786-e1bb-4ed9-bb30-4e074cd2b188
-- title:
--   Directed Sidorenko forces a homomorphism to the edge (Observation 20)
-- statement:
--   Observation 20 of the paper: if the oriented graph B has the directed Sidorenko property, then B has a homomorphism to the directed edge K_2. The proof evaluates the Sidorenko inequality on the complete balanced bipartite orientation on n + n vertices, all edges directed from the first part to the second: its directed edge density is one half, while a graph without a homomorphism to the directed edge has no homomorphisms into it at all, so the inequality fails for large n. The colouring supplied by the homomorphism is exactly the two-colouring recorded by homToEdge.
--
--   **Formalization Note** The complete balanced bipartite orientation is the concrete graph knn of the graph layer; the quantitative content is the growth of the homomorphism count against n^{2 e(B)}.
-- source:
--   J. Fox, Z. Himwich, N. Mani, Y. Zhou, A note on directed analogues of the Sidorenko and forcing conjectures, Electron. J. Combin. 32(3) (2025) #P3.38, Section 3 (Observation 20, page 8).

import Mathlib
import Definitions.Def_DirS_gr
import Definitions.Def_DirS_gw

namespace DirS

/-!  Milestone 4 (Observation 20): directed Sidorenko forces a homomorphism
to the edge. If the oriented graph B has the directed Sidorenko property,
then B has a homomorphism to the directed edge K_2. The proof evaluates
the Sidorenko inequality on the complete balanced bipartite orientation
on n + n vertices: a graph without a homomorphism to the edge has no
homomorphism into it at all, while its directed edge density is one half,
and the inequality fails for large n. -/
theorem dir_sid_needs_edge {m : ℕ} (B : OriGraph m) (h : DirSidorenko B) :
    homToEdge B := by sorry

end DirS
