-- Prove2me | Theorems.Thm_ConjCoord_Proof_r3_two_mul_eq
-- name    : ConjCoord.Proof.r3_two_mul_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:47:29.434734+00:00
-- url     : https://prove2.me/theorems/dfbec574-4cdf-4732-a4d9-d43bdca8a072
-- title:
--   Proof: r3 two mul eq
-- statement:
--   `r₃(2n) = 3 r_{1,1,2}(n)` for odd `n`.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Reps.lean#L181-L246
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Reps.lean#L181-L246

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Reps
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
variable {n : ℕ}

theorem ConjCoord.Proof.r3_two_mul_eq (hn : n % 2 = 1) : r3 (2 * n) = 3 * reps 1 1 2 n := by sorry
