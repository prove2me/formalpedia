-- Prove2me | Theorems.Thm_Conway99Formal_SrgCore_ones_square
-- name    : Conway99Formal.SrgCore.ones_square
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T04:09:12.324064+00:00
-- url     : https://prove2.me/theorems/01e581e7-fa40-4d82-a96e-d94acdee6acb
-- title:
--   Square of the all-ones matrix
-- statement:
--   For an SRG(99,14,1,2), over any ring the all-ones matrix on the 99 vertices satisfies
--
--   $$J^2=99J$$
--
--   Role: Each entry of J squared sums 99 ones.
-- source:
--   Exact original Lean source: formalization/2026-10-03/srg-core/Core.lean#L385-L390; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 64ce9b86d07bbdd11a61266b80c3043c34c08d7f939471fff2c44dc34ff37904. Mechanically extracted declaration: blob/a45708acebe3f397faccb1b646be906f24f23ee5/formalization/2026-10-03/srg-core/Core.lean#L385-L390.

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

theorem Conway99Formal.SrgCore.ones_square (h : G.IsSRGWith 99 14 1 2)
    (α : Type*) [Ring α] :
    (of 1 : Matrix V V α) * (of 1 : Matrix V V α) =
      99 • (of 1 : Matrix V V α) := by sorry
