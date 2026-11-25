-- Prove2me | Theorems.Thm_ConjCoord_reps112_eq
-- name    : ConjCoord.reps112_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:55:16.690393+00:00
-- url     : https://prove2.me/theorems/422fed98-e9f0-553f-bf1b-23a47f7be491
-- title:
--   Conj Coord: reps112 eq
-- statement:
--   Lemma 3: `r_{1,1,2}(n) = 2 r_{1,2,4}(n)` for odd `n`.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/Solution.lean#L55-L56
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/Solution.lean#L55-L56

module
public import Definitions.Def_ConjCoord
public import Definitions.Def_ConjCoord_Solution
public import Theorems.Thm_ConjCoord_Proof_reps112_eq

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord

theorem ConjCoord.reps112_eq {n : ℕ} (hn : n % 2 = 1) : reps 1 1 2 n = 2 * reps 1 2 4 n := by sorry
