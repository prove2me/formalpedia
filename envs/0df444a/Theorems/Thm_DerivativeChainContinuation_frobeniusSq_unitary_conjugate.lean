-- Prove2me | Theorems.Thm_DerivativeChainContinuation_frobeniusSq_unitary_conjugate
-- name    : DerivativeChainContinuation.frobeniusSq_unitary_conjugate
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T18:26:51.147983+00:00
-- url     : https://prove2.me/theorems/9a6b1f8c-0fae-4be9-ad77-8cab9212e1a9
-- title:
--   Frobenius energy is invariant under unitary conjugation
-- statement:
--   For complex square matrices $M,U$ with $U$ unitary, $$\|U^*MU\|_F^2=\|M\|_F^2.$$ This identity transports the compression energy to a Schur basis.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/FrobeniusTrace.lean#L16-L30

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CompressionGeometry
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem DerivativeChainContinuation.frobeniusSq_unitary_conjugate {n : ℕ} (M U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ unitaryGroup (Fin n) ℂ) :
    frobeniusSq (U.conjTranspose*M*U) = frobeniusSq M := by sorry
