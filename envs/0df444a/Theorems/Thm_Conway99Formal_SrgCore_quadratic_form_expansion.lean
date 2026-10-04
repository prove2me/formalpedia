-- Prove2me | Theorems.Thm_Conway99Formal_SrgCore_quadratic_form_expansion
-- name    : Conway99Formal.SrgCore.quadratic_form_expansion
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T02:48:30.550631+00:00
-- url     : https://prove2.me/theorems/e8f4ca14-bde8-4c95-8d2e-c3ee7b423d9d
-- title:
--   Adjacency quadratic-form expansion on a subset
-- statement:
--   For any vertex subset S in a graph satisfying the strongly regular parameters (99,14,1,2), the integer sum of (A²)ij over i,j in S equals 12|S| minus the integer adjacency-entry sum over i,j in S plus 2|S|², where A is the integer adjacency matrix.
-- source:
--   Exact original Lean source: formalization/2026-10-03/srg-core/Core.lean#L423-L453; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 64ce9b86d07bbd11a61266b80c3043c34c08d7f939471fff2c44dc34ff37904. Mechanically extracted declaration: blob/a45708acebe3f397faccb1b646be906f24f23ee5/formalization/2026-10-03/srg-core/Core.lean#L423-L453.

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

theorem Conway99Formal.SrgCore.quadratic_form_expansion (h : G.IsSRGWith 99 14 1 2)
    (S : Finset V) :
    (∑ i ∈ S, ∑ j ∈ S, (G.adjMatrix ℤ * G.adjMatrix ℤ) i j) =
      12 * (S.card : ℤ) -
        (∑ i ∈ S, ∑ j ∈ S, G.adjMatrix ℤ i j) + 2 * (S.card : ℤ) ^ 2 := by sorry
