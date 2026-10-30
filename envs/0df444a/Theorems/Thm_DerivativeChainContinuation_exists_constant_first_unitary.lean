-- Prove2me | Theorems.Thm_DerivativeChainContinuation_exists_constant_first_unitary
-- name    : DerivativeChainContinuation.exists_constant_first_unitary
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:48:13.731659+00:00
-- url     : https://prove2.me/theorems/c7d6fe23-4558-46fe-94d6-c661fe113268
-- title:
--   A unitary basis with prescribed constant first vector
-- statement:
--   For every $n\ge0$, there is an $(n+1)$-dimensional complex unitary matrix whose first column is the constant vector with entries $1/\sqrt{n+1}$.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/ConstantUnitary.lean#L9-L36

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem DerivativeChainContinuation.exists_constant_first_unitary (n : ℕ) :
    ∃ Q : Matrix (Fin (n+1)) (Fin (n+1)) ℂ,
      Q ∈ unitaryGroup (Fin (n+1)) ℂ ∧
      ∀ i, Q i 0 = ((Real.sqrt (n+1 : ℝ))⁻¹ : ℂ) := by sorry
