-- Prove2me | Theorems.Thm_Conway99Formal_SrgCore_ones_times_adjacency
-- name    : Conway99Formal.SrgCore.ones_times_adjacency
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T04:13:16.266958+00:00
-- url     : https://prove2.me/theorems/c10d8243-0038-43d4-9594-d0380b785f6e
-- title:
--   Every adjacency column sums to fourteen
-- statement:
--   For an SRG(99,14,1,2), over any commutative ring, multiplication of the all-ones matrix J by adjacency matrix A gives
--
--   $$JA=14J$$
--
--   Role: This is the column-sum counterpart of regularity.
-- source:
--   Exact original Lean source: formalization/2026-10-03/srg-core/Core.lean#L376-L383; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 64ce9b86d07bbdd11a61266b80c3043c34c08d7f939471fff2c44dc34ff37904. Mechanically extracted declaration: blob/a45708acebe3f397faccb1b646be906f24f23ee5/formalization/2026-10-03/srg-core/Core.lean#L376-L383.

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

theorem Conway99Formal.SrgCore.ones_times_adjacency (h : G.IsSRGWith 99 14 1 2)
    (α : Type*) [CommRing α] [DecidableEq α] :
    (of 1 : Matrix V V α) * G.adjMatrix α = 14 • (of 1 : Matrix V V α) := by sorry
