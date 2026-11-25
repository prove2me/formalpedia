-- Prove2me | Theorems.Thm_ConjCoord_Proof_r3_eq_three_mul_reps122
-- name    : ConjCoord.Proof.r3_eq_three_mul_reps122
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:46:50.930527+00:00
-- url     : https://prove2.me/theorems/9a17eedf-44ae-5507-8b0e-2778cd5feddb
-- title:
--   Proof: r3 eq three mul reps122
-- statement:
--   `r₃(n) = 3 r_{1,2,2}(n)` for `n ≡ 1 (mod 4)`.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Reps.lean#L117-L178
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Reps.lean#L117-L178

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Reps
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
variable {n : ℕ}

theorem ConjCoord.Proof.r3_eq_three_mul_reps122 (hn : n % 4 = 1) : r3 n = 3 * reps 1 2 2 n := by sorry
