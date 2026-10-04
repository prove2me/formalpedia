-- Prove2me | Theorems.Thm_Conway99Formal_SrgCore_half_internal_degree_sum_eq_induced_edges
-- name    : Conway99Formal.SrgCore.half_internal_degree_sum_eq_induced_edges
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T04:08:55.339221+00:00
-- url     : https://prove2.me/theorems/6696625a-5e6b-465c-8b04-e953251db3ce
-- title:
--   Induced edge count from internal degrees
-- statement:
--   For any finite vertex subset S in a finite simple graph, half the sum of the internal degrees equals the number of edges in the induced subgraph
--
--   $$\frac{1}{2}\sum_{u\in S}|N(u)\cap S|=|E(G[S])|$$
--
--   Role: Each induced edge contributes once at each endpoint.
-- source:
--   Exact original Lean source: formalization/2026-10-03/srg-core/Core.lean#L153-L157; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 64ce9b86d07bbdd11a61266b80c3043c34c08d7f939471fff2c44dc34ff37904. Mechanically extracted declaration: blob/a45708acebe3f397faccb1b646be906f24f23ee5/formalization/2026-10-03/srg-core/Core.lean#L153-L157.

import Mathlib

namespace Conway99Formal.SrgCore
end Conway99Formal.SrgCore

set_option autoImplicit false

/-! Graph-owned parameter and adjacency identities for a hypothetical SRG(99,14,1,2).
Sources: `Conway99/Conway99/Core.lean` §§1–3, 8.1;
`Conway99/Conway99/Claims/C01srgcorealgebra.lean` §§0, 3, 6;
`Conway99/results/R005_star_complement_square_discriminant.md`.
-/

open Conway99Formal.SrgCore

open SimpleGraph Matrix Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem Conway99Formal.SrgCore.half_internal_degree_sum_eq_induced_edges (S : Finset V) :
    (∑ u ∈ S, (S ∩ G.neighborFinset u).card) / 2 =
      (G.induce (S : Set V)).edgeFinset.card := by sorry
