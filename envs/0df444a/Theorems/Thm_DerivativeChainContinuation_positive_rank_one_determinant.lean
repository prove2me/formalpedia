-- Prove2me | Theorems.Thm_DerivativeChainContinuation_positive_rank_one_determinant
-- name    : DerivativeChainContinuation.positive_rank_one_determinant
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:18:30.30821+00:00
-- url     : https://prove2.me/theorems/a096940d-4b91-4993-9de9-9bdf2b783de9
-- title:
--   Positive rank-one updates increase determinant norm
-- statement:
--   For a finite positive definite complex matrix $A$ and complex vector $u$, $$|\det A|\le|\det(A+uu^*)|.$$
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/PositiveRankOne.lean#L8-L28

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix
open scoped BigOperators ComplexOrder

theorem DerivativeChainContinuation.positive_rank_one_determinant {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) (u : Fin n → ℂ) :
    ‖A.det‖ ≤ ‖(A+vecMulVec u (star u)).det‖ := by sorry
