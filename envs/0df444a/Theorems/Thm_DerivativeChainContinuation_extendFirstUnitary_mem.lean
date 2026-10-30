-- Prove2me | Theorems.Thm_DerivativeChainContinuation_extendFirstUnitary_mem
-- name    : DerivativeChainContinuation.extendFirstUnitary_mem
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T18:21:35.587762+00:00
-- url     : https://prove2.me/theorems/809aa29a-bf51-413b-ba73-9a26df2b96bd
-- title:
--   Extending a unitary matrix by one fixed coordinate
-- statement:
--   If $U$ is a complex unitary $n\times n$ matrix, its block extension $$\operatorname{diag}(1,U)$$ is unitary in dimension $n+1$.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/SchurExtension.lean#L13-L28

import Mathlib
import Definitions.Def_DerivativeChainContinuation_SchurExtension
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem DerivativeChainContinuation.extendFirstUnitary_mem {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ unitaryGroup (Fin n) ℂ) :
    extendFirstUnitary U ∈ unitaryGroup (Fin (n+1)) ℂ := by sorry
