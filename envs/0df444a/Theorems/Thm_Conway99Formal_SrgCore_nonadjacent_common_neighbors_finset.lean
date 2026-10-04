-- Prove2me | Theorems.Thm_Conway99Formal_SrgCore_nonadjacent_common_neighbors_finset
-- name    : Conway99Formal.SrgCore.nonadjacent_common_neighbors_finset
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T03:21:39.384351+00:00
-- url     : https://prove2.me/theorems/732e43db-4213-4922-beb5-61a8385d8ca1
-- title:
--   Nonadjacent vertices have two common neighbors
-- statement:
--   In an SRG(99,14,1,2), distinct nonadjacent vertices u and v have exactly two common neighbors.
--
--   $$|N(u)\cap N(v)|=2\qquad(u\ne v,\ uv\notin E(G))$$
--
--   Role: The statement uses the intersection of the two finite neighbor sets.
-- source:
--   Exact original Lean source: formalization/2026-10-03/srg-core/Core.lean#L47-L60; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 64ce9b86d07bbd11a61266b80c3043c34c08d7f939471fff2c44dc34ff37904. Mechanically extracted declaration: blob/a45708acebe3f397faccb1b646be906f24f23ee5/formalization/2026-10-03/srg-core/Core.lean#L47-L60.

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

theorem Conway99Formal.SrgCore.nonadjacent_common_neighbors_finset (h : G.IsSRGWith 99 14 1 2)
    (u v : V) (hne : u ≠ v) (huv : ¬ G.Adj u v) :
    (G.neighborFinset u ∩ G.neighborFinset v).card = 2 := by sorry
