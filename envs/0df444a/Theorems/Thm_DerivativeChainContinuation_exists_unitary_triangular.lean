-- Prove2me | Theorems.Thm_DerivativeChainContinuation_exists_unitary_triangular
-- name    : DerivativeChainContinuation.exists_unitary_triangular
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T18:24:08.414298+00:00
-- url     : https://prove2.me/theorems/c4c6cc31-7fcc-4c56-877b-7ef0df46fe6a
-- title:
--   Finite-dimensional complex unitary triangularization
-- statement:
--   Every complex square matrix $A$ admits a unitary $U$ for which $$U^*AU$$ is upper triangular. The statement includes dimension zero and is the classical Schur triangularization theorem.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/SchurTriangular.lean#L8-L36

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem DerivativeChainContinuation.exists_unitary_triangular (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ U : Matrix (Fin n) (Fin n) ℂ,
      U ∈ unitaryGroup (Fin n) ℂ ∧ (U.conjTranspose*A*U).IsUpperTriangular := by sorry
