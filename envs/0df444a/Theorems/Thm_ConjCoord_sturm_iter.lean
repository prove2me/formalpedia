-- Prove2me | Theorems.Thm_ConjCoord_sturm_iter
-- name    : ConjCoord.sturm_iter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:55:45.827988+00:00
-- url     : https://prove2.me/theorems/678db4eb-9408-4c8a-9c1f-6ccb117d35be
-- title:
--   Conj Coord: sturm iter
-- statement:
--   Sturm's theorem modulo `2`, applied `k` times.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/Solution.lean#L34-L36
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/Solution.lean#L34-L36

module
public import Definitions.Def_ConjCoord
public import Definitions.Def_ConjCoord_Solution
public import Theorems.Thm_ConjCoord_Proof_sturm_iter

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord

theorem ConjCoord.sturm_iter {f : ℕ → ℤ} {B : ℕ} (S : SturmInput f B) (k : ℕ) :
    ∀ g ∈ S.M, (∀ n ≤ B, (2 : ℤ) ^ k ∣ g n) → ∀ n, (2 : ℤ) ^ k ∣ g n := by sorry
