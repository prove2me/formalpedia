-- Prove2me | Theorems.Thm_Conway99Formal_SrgCore_diagonal_two_walk
-- name    : Conway99Formal.SrgCore.diagonal_two_walk
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T04:13:30.807196+00:00
-- url     : https://prove2.me/theorems/b3656608-6b7a-4034-9dfd-51c8e0adc124
-- title:
--   Closed two-walk count at each vertex
-- statement:
--   For every vertex u in an SRG(99,14,1,2), the integer adjacency matrix A satisfies
--
--   $$\sum_w A_{uw}A_{wu}=14$$
--
--   Role: The closed length-two walks counted here correspond to the 14 neighbors of u.
-- source:
--   Exact original Lean source: formalization/2026-10-03/srg-core/Core.lean#L415-L421; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 64ce9b86d07bbdd11a61266b80c3043c34c08d7f939471fff2c44dc34ff37904. Mechanically extracted declaration: blob/a45708acebe3f397faccb1b646be906f24f23ee5/formalization/2026-10-03/srg-core/Core.lean#L415-L421.

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

theorem Conway99Formal.SrgCore.diagonal_two_walk (h : G.IsSRGWith 99 14 1 2) (u : V) :
    (∑ w, G.adjMatrix ℤ u w * G.adjMatrix ℤ w u) = 14 := by sorry
