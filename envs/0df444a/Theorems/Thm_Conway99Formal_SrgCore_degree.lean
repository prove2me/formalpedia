-- Prove2me | Theorems.Thm_Conway99Formal_SrgCore_degree
-- name    : Conway99Formal.SrgCore.degree
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T03:55:38.714077+00:00
-- url     : https://prove2.me/theorems/333e14e4-f868-4da8-942e-0f9abca1f5ca
-- title:
--   Every vertex has degree fourteen
-- statement:
--   If G has strongly regular parameters (99,14,1,2), each vertex v has degree
--
--   $$\deg_G(v)=14$$
--
--   Role: This is the regularity parameter of the graph.
-- source:
--   Exact original Lean source: formalization/2026-10-03/srg-core/Core.lean#L20-L21; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 64ce9b86d07bbdd11a61266b80c3043c34c08d7f939471fff2c44dc34ff37904. Mechanically extracted declaration: blob/a45708acebe3f397faccb1b646be906f24f23ee5/formalization/2026-10-03/srg-core/Core.lean#L20-L21.

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

theorem Conway99Formal.SrgCore.degree (h : G.IsSRGWith 99 14 1 2) (v : V) : G.degree v = 14 := by sorry
