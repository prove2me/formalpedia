-- Prove2me | Theorems.Thm_Conway99Formal_SrgCore_complement_adjacency
-- name    : Conway99Formal.SrgCore.complement_adjacency
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T03:32:01.393191+00:00
-- url     : https://prove2.me/theorems/24562d19-c521-41dc-9909-9d35c4154477
-- title:
--   Adjacency matrix of the graph complement
-- statement:
--   For a finite simple graph G, over any ring with decidable equality, the complement graph has adjacency matrix equal to all ones minus the identity and the original adjacency matrix
--
--   $$A(G^c)=J-I-A(G)$$
--
--   Role: J is the all-ones matrix, I is the identity, and A(G) uses the same coefficient ring.
-- source:
--   Exact original Lean source: formalization/2026-10-03/srg-core/Core.lean#L336-L340; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 64ce9b86d07bbdd11a61266b80c3043c34c08d7f939471fff2c44dc34ff37904. Mechanically extracted declaration: blob/a45708acebe3f397faccb1b646be906f24f23ee5/formalization/2026-10-03/srg-core/Core.lean#L336-L340.

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

theorem Conway99Formal.SrgCore.complement_adjacency (α : Type*) [Ring α] [DecidableEq α] :
    Gᶜ.adjMatrix α = (of 1 : Matrix V V α) - 1 - G.adjMatrix α := by sorry
