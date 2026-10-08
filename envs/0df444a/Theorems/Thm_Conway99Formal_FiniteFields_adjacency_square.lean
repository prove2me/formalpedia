-- Prove2me | Theorems.Thm_Conway99Formal_FiniteFields_adjacency_square
-- name    : Conway99Formal.FiniteFields.adjacency_square
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T19:04:38.556887+00:00
-- url     : https://prove2.me/theorems/d0624224-25ff-43b3-a679-9256b03cdfd0
-- title:
--   SRG adjacency-square identity over a ring
-- statement:
--   Let G be a finite simple graph on V with SRG parameters (99,14,1,2), R a ring with decidable equality, A_R its adjacency matrix, I the identity, and J_R the all-ones matrix. Then \[A_R^2=12I-A_R+2J_R.\]
-- source:
--   Exact original Lean source: formalization/2026-10-03/finite-fields/FiniteFieldCore.lean#22-29; source commit a45708acebe3f397faccb1b646be906f24f23ee5; source SHA-256 52326ff98a127ff606cee76db5da2a628c54fc39f4086a588480d56663b6d983. Mechanically extracted declaration: blob/a45708acebe3f397faccb1b646be906f24f23ee5/formalization/2026-10-03/finite-fields/FiniteFieldCore.lean#L22-L29.

import Definitions.Def_FiniteFieldCore
import Mathlib

namespace Conway99Formal.FiniteFields
end Conway99Formal.FiniteFields

set_option autoImplicit false

open Conway99Formal.FiniteFields

open Matrix SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem Conway99Formal.FiniteFields.adjacency_square {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : G.IsSRGWith 99 14 1 2) (R : Type*) [Ring R] [DecidableEq R] :
    (G.adjMatrix R) ^ 2 = 12 • (1 : Matrix V V R) - G.adjMatrix R + 2 • J R := by sorry
