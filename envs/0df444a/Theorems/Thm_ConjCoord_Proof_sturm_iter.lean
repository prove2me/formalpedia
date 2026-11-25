-- Prove2me | Theorems.Thm_ConjCoord_Proof_sturm_iter
-- name    : ConjCoord.Proof.sturm_iter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:52:08.558545+00:00
-- url     : https://prove2.me/theorems/aaba462b-ad46-4937-b7ca-d2eeb5b4d8a3
-- title:
--   Proof: sturm iter
-- statement:
--   Sturm's theorem applied `k` times.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Main.lean#L25-L44
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/Main.lean#L25-L44

module
public import Definitions.Def_ConjCoord_Compute
public import Definitions.Def_ConjCoord_TwoSquares
public import Definitions.Def_ConjCoord_Main
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof

theorem ConjCoord.Proof.sturm_iter {f : ℕ → ℤ} {B : ℕ} (S : SturmInput f B) (k : ℕ) :
    ∀ g ∈ S.M, (∀ n ≤ B, (2 : ℤ) ^ k ∣ g n) → ∀ n, (2 : ℤ) ^ k ∣ g n := by sorry
