-- Prove2me | Theorems.Thm_BandParity_quadraticChar_of_char_one
-- name    : BandParity.quadraticChar_of_char_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:07:42.750377+00:00
-- url     : https://prove2.me/theorems/fc774cc5-eb24-4c7c-a308-46f95b908718
-- title:
--   Band Parity: quadratic Char of char one
-- statement:
--   The Band Parity construction uses the quadratic Char of char one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L199-L201
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L199-L201

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

theorem BandParity.quadraticChar_of_char_one {x : ZMod p} (hx : x ≠ 0) (h : χ x = 1 ∨ χ x = -1) :
    quadraticChar (ZMod p) x = 1 := by sorry
