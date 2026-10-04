-- Prove2me | Theorems.Thm_Conway99Formal_SrgCore_far_pair_common_neighbor_row
-- name    : Conway99Formal.SrgCore.far_pair_common_neighbor_row
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T02:48:16.620355+00:00
-- url     : https://prove2.me/theorems/f70780a3-1067-462b-9448-d707bc376e29
-- title:
--   Adjacency and common-neighbor row identity
-- statement:
--   For any distinct vertices u and v in a graph satisfying the strongly regular parameters (99,14,1,2), the integer sum over w of A(u,w)A(v,w), plus A(u,v), is 2, where A is the integer adjacency matrix. The sum is therefore 1 for adjacent pairs and 2 for nonadjacent pairs.
-- source:
--   Exact original Lean source: formalization/2026-10-03/srg-core/Core.lean#L401-L413; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 64ce9b86d07bbd11a61266b80c3043c34c08d7f939471fff2c44dc34ff37904. Mechanically extracted declaration: blob/a45708acebe3f397faccb1b646be906f24f23ee5/formalization/2026-10-03/srg-core/Core.lean#L401-L413.

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

theorem Conway99Formal.SrgCore.far_pair_common_neighbor_row (h : G.IsSRGWith 99 14 1 2)
    (u v : V) (huv : u ≠ v) :
    (∑ w, G.adjMatrix ℤ u w * G.adjMatrix ℤ v w) + G.adjMatrix ℤ u v = 2 := by sorry
