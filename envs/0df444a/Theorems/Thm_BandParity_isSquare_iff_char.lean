-- Prove2me | Theorems.Thm_BandParity_isSquare_iff_char
-- name    : BandParity.isSquare_iff_char
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:06:15.548972+00:00
-- url     : https://prove2.me/theorems/7d85ba44-3338-425e-9117-733d0f693ebb
-- title:
--   Band Parity: is Square iff char
-- statement:
--   The Band Parity construction uses the is Square iff char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L175-L197
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L175-L197

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

theorem BandParity.isSquare_iff_char {x : ZMod p} (hx : x ≠ 0) : IsSquare x ↔ (χ x = 1 ∨ χ x = -1) := by sorry
