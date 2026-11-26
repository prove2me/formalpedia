-- Prove2me | Theorems.Thm_BandParity_quadraticChar_of_char_gi
-- name    : BandParity.quadraticChar_of_char_gi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:08:00.56229+00:00
-- url     : https://prove2.me/theorems/edfae645-0b26-494d-94bc-698f3916ab81
-- title:
--   Band Parity: quadratic Char of char gi
-- statement:
--   The Band Parity construction uses the quadratic Char of char gi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L203-L206
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L203-L206

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ

theorem BandParity.quadraticChar_of_char_gi {x : ZMod p} (hx : x ≠ 0) (h : χ x = gi ∨ χ x = -gi) :
    quadraticChar (ZMod p) x = -1 := by sorry
