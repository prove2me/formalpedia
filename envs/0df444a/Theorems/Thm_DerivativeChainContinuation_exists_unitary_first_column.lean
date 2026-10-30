-- Prove2me | Theorems.Thm_DerivativeChainContinuation_exists_unitary_first_column
-- name    : DerivativeChainContinuation.exists_unitary_first_column
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T18:19:36.318668+00:00
-- url     : https://prove2.me/theorems/aeb10b72-0e15-4d7d-ad37-529e98c12b87
-- title:
--   Unitary conjugation clears the first subdiagonal column
-- statement:
--   For every complex $(n+1)\times(n+1)$ matrix $A$, there is a unitary $Q$ such that $$(Q^*AQ)_{i+1,0}=0\quad(0\le i<n).$$ The first basis vector is an eigenvector.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/SchurFirstColumn.lean#L8-L35

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem DerivativeChainContinuation.exists_unitary_first_column (n : ℕ)
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    ∃ Q : Matrix (Fin (n+1)) (Fin (n+1)) ℂ,
      Q ∈ unitaryGroup (Fin (n+1)) ℂ ∧
      ∀ i : Fin n, (Q.conjTranspose*A*Q) i.succ 0 = 0 := by sorry
