-- Prove2me | Theorems.Thm_BandParity_card_cls
-- name    : BandParity.card_cls
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:04:58.266293+00:00
-- url     : https://prove2.me/theorems/e4793e40-a10b-430b-bbd2-f4dce1a70d89
-- title:
--   Band Parity: card cls
-- statement:
--   The Band Parity construction uses the card cls property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L119-L123
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L119-L123

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

theorem BandParity.card_cls {z : GaussianInt} (hz : z = 1 ∨ z = gi ∨ z = -1 ∨ z = -gi) :
    (cls χ z).card = (p - 1) / 4 := by sorry
