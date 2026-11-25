-- Prove2me | Theorems.Thm_ConjCoord_two_sq_unique
-- name    : ConjCoord.two_sq_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:56:03.796346+00:00
-- url     : https://prove2.me/theorems/aedf83e3-ae34-5493-afd9-21f814d007de
-- title:
--   Conj Coord: two sq unique
-- statement:
--   Uniqueness of the representation of an odd prime as a sum of two squares, with the even
--   square second.
--
--   Source: https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/Solution.lean#L67-L70
-- source:
--   https://github.com/jkfarland-bot/ConjCoord/blob/c956f4808ba6c6f15a1d4234a04cd8fc56be2711/Solution.lean#L67-L70

module
public import Definitions.Def_ConjCoord
public import Definitions.Def_ConjCoord_Solution
public import Theorems.Thm_ConjCoord_Proof_two_sq_unique

set_option autoImplicit true
@[expose] public section
public section
open Finset
open ConjCoord

theorem ConjCoord.two_sq_unique {p : ℤ} (hp : Prime p) (hodd : p % 2 = 1) {α β γ δ : ℤ} (hα : 0 < α)
    (hβ : 0 < β) (hγ : 0 < γ) (hδ : 0 < δ) (h1 : α ^ 2 + β ^ 2 = p) (h2 : γ ^ 2 + δ ^ 2 = p)
    (hβe : Even β) (hδe : Even δ) : α = γ ∧ β = δ := by sorry
