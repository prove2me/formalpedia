-- Prove2me | Theorems.Thm_ConjCoord_Proof_two_sq_unique
-- name    : ConjCoord.Proof.two_sq_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:50:05.173904+00:00
-- url     : https://prove2.me/theorems/16ce3a8c-17ab-5a36-a92c-4b483372ceda
-- title:
--   Proof: two sq unique
-- statement:
--   Uniqueness of the representation of an odd prime as a sum of two squares, with the even
--   square second.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/TwoSquares.lean#L32-L86
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/ConjCoord/TwoSquares.lean#L32-L86

module
public import Definitions.Def_ConjCoord_Reps
public import Definitions.Def_ConjCoord_TwoSquares
set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord ConjCoord.Proof

theorem ConjCoord.Proof.two_sq_unique {p : ℤ} (hp : Prime p) (hodd : p % 2 = 1) {α β γ δ : ℤ} (hα : 0 < α)
    (hβ : 0 < β) (hγ : 0 < γ) (hδ : 0 < δ) (h1 : α ^ 2 + β ^ 2 = p) (h2 : γ ^ 2 + δ ^ 2 = p)
    (hβe : Even β) (hδe : Even δ) : α = γ ∧ β = δ := by sorry
