-- Prove2me | Theorems.Thm_Conway99Formal_SrgCore_internal_degree_half_sum
-- name    : Conway99Formal.SrgCore.internal_degree_half_sum
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T03:55:42.992631+00:00
-- url     : https://prove2.me/theorems/f5b78cb5-e02c-4699-b4af-3725f74cc387
-- title:
--   Internal degree sum is even
-- statement:
--   For any finite vertex subset S, the sum of internal degrees is even; its half, rounded down by natural-number division, doubles back to the full sum
--
--   $$2\left\lfloor\frac{\sum_{u\in S}|N(u)\cap S|}{2}\right\rfloor=\sum_{u\in S}|N(u)\cap S|$$
--
--   Role: This is the parity component of the handshaking identity.
-- source:
--   Exact original Lean source: formalization/2026-10-03/srg-core/Core.lean#L147-L151; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 64ce9b86d07bbdd11a61266b80c3043c34c08d7f939471fff2c44dc34ff37904. Mechanically extracted declaration: blob/a45708acebe3f397faccb1b646be906f24f23ee5/formalization/2026-10-03/srg-core/Core.lean#L147-L151.

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

theorem Conway99Formal.SrgCore.internal_degree_half_sum (S : Finset V) :
    2 * ((∑ u ∈ S, (S ∩ G.neighborFinset u).card) / 2) =
      ∑ u ∈ S, (S ∩ G.neighborFinset u).card := by sorry
