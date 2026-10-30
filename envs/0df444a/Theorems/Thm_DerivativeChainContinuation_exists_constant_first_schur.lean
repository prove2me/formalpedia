-- Prove2me | Theorems.Thm_DerivativeChainContinuation_exists_constant_first_schur
-- name    : DerivativeChainContinuation.exists_constant_first_schur
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:50:18.853338+00:00
-- url     : https://prove2.me/theorems/535bc632-1cae-462c-9ddf-9a190989ca1e
-- title:
--   Schur triangularization preserving the constant first vector
-- statement:
--   For any list of $n+1$ complex source slots, its ambient root compression has a unitary triangularization whose first column is the constant unit vector. Thus the zero compression direction remains fixed while the remaining block is triangularized.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/PinnedSchur.lean#L10-L38

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CompressionGeometry
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem DerivativeChainContinuation.exists_constant_first_schur (n : ℕ) (a : Fin (n+1) → ℂ) :
    ∃ Q : Matrix (Fin (n+1)) (Fin (n+1)) ℂ,
      Q ∈ unitaryGroup (Fin (n+1)) ℂ ∧
      (∀ i, Q i 0=((Real.sqrt (n+1:ℝ))⁻¹:ℂ)) ∧
      (Q.conjTranspose*rootCompression a*Q).IsUpperTriangular := by sorry
