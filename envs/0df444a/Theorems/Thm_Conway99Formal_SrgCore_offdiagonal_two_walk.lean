-- Prove2me | Theorems.Thm_Conway99Formal_SrgCore_offdiagonal_two_walk
-- name    : Conway99Formal.SrgCore.offdiagonal_two_walk
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T04:13:28.963987+00:00
-- url     : https://prove2.me/theorems/a5408dfb-fad9-4a8c-ad62-2099665059d4
-- title:
--   Off-diagonal two-walk count
-- statement:
--   For distinct vertices u and v in an SRG(99,14,1,2), let A be the integer adjacency matrix. The number of length-two walks from u to v, plus the adjacency indicator of uv, equals
--
--   $$\sum_w A_{uw}A_{wv}+A_{uv}=2$$
--
--   Role: Thus adjacent pairs have one common neighbor and distinct nonadjacent pairs have two.
-- source:
--   Exact original Lean source: formalization/2026-10-03/srg-core/Core.lean#L392-L399; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 64ce9b86d07bbdd11a61266b80c3043c34c08d7f939471fff2c44dc34ff37904. Mechanically extracted declaration: blob/a45708acebe3f397faccb1b646be906f24f23ee5/formalization/2026-10-03/srg-core/Core.lean#L392-L399.

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

theorem Conway99Formal.SrgCore.offdiagonal_two_walk (h : G.IsSRGWith 99 14 1 2)
    (u v : V) (huv : u ≠ v) :
    (∑ w, G.adjMatrix ℤ u w * G.adjMatrix ℤ w v) + G.adjMatrix ℤ u v = 2 := by sorry
