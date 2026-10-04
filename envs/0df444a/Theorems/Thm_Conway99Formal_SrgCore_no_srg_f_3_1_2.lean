-- Prove2me | Theorems.Thm_Conway99Formal_SrgCore_no_srg_f_3_1_2
-- name    : Conway99Formal.SrgCore.no_srg_f_3_1_2
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T04:09:00.178429+00:00
-- url     : https://prove2.me/theorems/2682b384-6fef-463c-acb1-109e042f5b2f
-- title:
--   No positive-order SRG has parameters (f,3,1,2)
-- statement:
--   For every positive natural number f, no finite simple graph of order f is strongly regular with valency 3, adjacent common-neighbor parameter 1, and nonadjacent common-neighbor parameter 2
--
--   $$f>0\quad\Longrightarrow\quad\neg\mathrm{SRG}(f,3,1,2)$$
--
--   Role: The theorem rules out this entire parameter family.
-- source:
--   Exact original Lean source: formalization/2026-10-03/srg-core/Core.lean#L175-L180; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 64ce9b86d07bbdd11a61266b80c3043c34c08d7f939471fff2c44dc34ff37904. Mechanically extracted declaration: blob/a45708acebe3f397faccb1b646be906f24f23ee5/formalization/2026-10-03/srg-core/Core.lean#L175-L180.

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

theorem Conway99Formal.SrgCore.no_srg_f_3_1_2 {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (f : ℕ) (hne : 0 < f) :
    ¬ H.IsSRGWith f 3 1 2 := by sorry
