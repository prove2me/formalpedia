-- Prove2me | Theorems.Thm_ConjCoord_phi_check
-- name    : ConjCoord.phi_check
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:58:49.703468+00:00
-- url     : https://prove2.me/theorems/ac57568b-3616-4d09-9bc9-42a7bbb5d955
-- title:
--   Conj Coord: phi check
-- statement:
--   The finite check for `Φ`: `256 ∣ Φ(n)` for `n ≤ 512`, the Sturm bound.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/Solution.lean#L30-L31
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/Solution.lean#L30-L31

module
public import Definitions.Def_ConjCoord
public import Definitions.Def_ConjCoord_Solution
public import Theorems.Thm_ConjCoord_Proof_phi_check

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord

theorem ConjCoord.phi_check (n : ℕ) (hn : n ≤ 512) : (256 : ℤ) ∣ phi n := by sorry
