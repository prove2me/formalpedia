-- Prove2me | Theorems.Thm_Conway99Formal_SrgCore_adjacency_double_sum_internal_degrees
-- name    : Conway99Formal.SrgCore.adjacency_double_sum_internal_degrees
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T03:21:17.49768+00:00
-- url     : https://prove2.me/theorems/cd34e2d5-6c79-4ec8-aa18-e8e31adaea3f
-- title:
--   Adjacency sum equals total internal degree
-- statement:
--   For any finite vertex subset S, the integer adjacency sum over ordered pairs in S equals the sum of internal degrees.
--
--   $$\sum_{i\in S}\sum_{j\in S}A_{ij}=\sum_{u\in S}|N(u)\cap S|$$
--
--   Role: This is a double-counting identity and needs no SRG premise.
-- source:
--   Exact original Lean source: formalization/2026-10-03/srg-core/Core.lean#L103-L119; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 64ce9b86d07bbd11a61266b80c3043c34c08d7f939471fff2c44dc34ff37904. Mechanically extracted declaration: blob/a45708acebe3f397faccb1b646be906f24f23ee5/formalization/2026-10-03/srg-core/Core.lean#L103-L119.

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

theorem Conway99Formal.SrgCore.adjacency_double_sum_internal_degrees (S : Finset V) :
    (∑ i ∈ S, ∑ j ∈ S, G.adjMatrix ℤ i j) =
      ∑ u ∈ S, ((S ∩ G.neighborFinset u).card : ℤ) := by sorry
