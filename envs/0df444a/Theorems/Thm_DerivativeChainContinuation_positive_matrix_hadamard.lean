-- Prove2me | Theorems.Thm_DerivativeChainContinuation_positive_matrix_hadamard
-- name    : DerivativeChainContinuation.positive_matrix_hadamard
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:02:07.795905+00:00
-- url     : https://prove2.me/theorems/16b46c3a-fef8-4dab-ae0e-d12c92930235
-- title:
--   Hadamard determinant bound for positive definite complex matrices
-- statement:
--   For a finite positive definite complex matrix $A$, $$|\det A|\le\prod_i\operatorname{Re}(A_{ii}).$$ This classical matrix inequality is proved as a dependency of the all-scale compression package.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/PositiveHadamard.lean#L9-L37

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix
open scoped BigOperators ComplexOrder

theorem DerivativeChainContinuation.positive_matrix_hadamard {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosDef) : ‖A.det‖ ≤ ∏ i, (A i i).re := by sorry
