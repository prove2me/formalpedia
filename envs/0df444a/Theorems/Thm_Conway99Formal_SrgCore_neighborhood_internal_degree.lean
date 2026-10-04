-- Prove2me | Theorems.Thm_Conway99Formal_SrgCore_neighborhood_internal_degree
-- name    : Conway99Formal.SrgCore.neighborhood_internal_degree
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T03:21:28.145327+00:00
-- url     : https://prove2.me/theorems/9a62467a-40ed-4c4f-9e11-5bbf71077dd6
-- title:
--   Adjacent vertices have one common neighbor
-- statement:
--   In an SRG(99,14,1,2), adjacent vertices u and v have exactly one common neighbor.
--
--   $$|N(u)\cap N(v)|=1\qquad(uv\in E(G))$$
--
--   Role: This is the adjacent common-neighbor condition in finite-set form.
-- source:
--   Exact original Lean source: formalization/2026-10-03/srg-core/Core.lean#L32-L45; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 64ce9b86d07bbd11a61266b80c3043c34c08d7f939471fff2c44dc34ff37904. Mechanically extracted declaration: blob/a45708acebe3f397faccb1b646be906f24f23ee5/formalization/2026-10-03/srg-core/Core.lean#L32-L45.

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

theorem Conway99Formal.SrgCore.neighborhood_internal_degree (h : G.IsSRGWith 99 14 1 2)
    (u v : V) (huv : G.Adj u v) :
    (G.neighborFinset u ∩ G.neighborFinset v).card = 1 := by sorry
