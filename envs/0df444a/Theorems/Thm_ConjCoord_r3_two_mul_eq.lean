-- Prove2me | Theorems.Thm_ConjCoord_r3_two_mul_eq
-- name    : ConjCoord.r3_two_mul_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:55:10.164605+00:00
-- url     : https://prove2.me/theorems/68cbb798-f88b-5104-86b1-38fd8d11beab
-- title:
--   Conj Coord: r3 two mul eq
-- statement:
--   Lemma 3: `r₃(2n) = 3 r_{1,1,2}(n)` for odd `n`.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/Solution.lean#L51-L52
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/Solution.lean#L51-L52

module
public import Definitions.Def_ConjCoord
public import Definitions.Def_ConjCoord_Solution
public import Theorems.Thm_ConjCoord_Proof_r3_two_mul_eq

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord

theorem ConjCoord.r3_two_mul_eq {n : ℕ} (hn : n % 2 = 1) : r3 (2 * n) = 3 * reps 1 1 2 n := by sorry
