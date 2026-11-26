-- Prove2me | Theorems.Thm_BandParity_char_neg
-- name    : BandParity.char_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:00:48.377793+00:00
-- url     : https://prove2.me/theorems/2182dcb8-16bf-5cb4-99fd-86607536e7d3
-- title:
--   Band Parity: char neg
-- statement:
--   The Band Parity construction uses the char neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L188-L189
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L188-L189

module
public import Definitions.Def_BandParity_Defs
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_Laws
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ
omit hχ

theorem BandParity.char_neg (hodd : χ (-1) = -1) (x : ZMod p) : χ (-x) = -χ x := by sorry
