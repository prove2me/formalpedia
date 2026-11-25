-- Prove2me | Theorems.Thm_ConjCoord_Proof_reps112_eq
-- name    : ConjCoord.Proof.reps112_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:47:03.120907+00:00
-- url     : https://prove2.me/theorems/1c1fc6f1-ceee-51fc-8202-764597e377d6
-- title:
--   Proof: reps112 eq
-- statement:
--   `r_{1,1,2}(n) = 2 r_{1,2,4}(n)` for odd `n`.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Reps.lean#L249-L289
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Reps.lean#L249-L289

module
public import Definitions.Def_ConjCoord_Defs
public import Definitions.Def_ConjCoord_Reps
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof
variable {n : ℕ}

theorem ConjCoord.Proof.reps112_eq (hn : n % 2 = 1) : reps 1 1 2 n = 2 * reps 1 2 4 n := by sorry
