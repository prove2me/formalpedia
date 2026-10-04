-- Prove2me | Theorems.Thm_Conway99Formal_SrgCore_adjacency_polynomial
-- name    : Conway99Formal.SrgCore.adjacency_polynomial
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T04:13:43.315456+00:00
-- url     : https://prove2.me/theorems/b649dde1-3346-48b9-a33e-fe659d40b22d
-- title:
--   Factored adjacency-matrix identity
-- statement:
--   If G has strongly regular parameters (99,14,1,2), then over any commutative ring its adjacency matrix A satisfies
--
--   $$(A-3I)(A+4I)=2J$$
--
--   Role: This is the factored form of the Conway adjacency identity.
-- source:
--   Exact original Lean source: formalization/2026-10-03/srg-core/Core.lean#L351-L363; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 64ce9b86d07bbdd11a61266b80c3043c34c08d7f939471fff2c44dc34ff37904. Mechanically extracted declaration: blob/a45708acebe3f397faccb1b646be906f24f23ee5/formalization/2026-10-03/srg-core/Core.lean#L351-L363.

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

theorem Conway99Formal.SrgCore.adjacency_polynomial (h : G.IsSRGWith 99 14 1 2)
    (α : Type*) [CommRing α] [DecidableEq α] :
    (G.adjMatrix α - 3 • (1 : Matrix V V α)) *
      (G.adjMatrix α + 4 • (1 : Matrix V V α)) =
        2 • (of 1 : Matrix V V α) := by sorry
