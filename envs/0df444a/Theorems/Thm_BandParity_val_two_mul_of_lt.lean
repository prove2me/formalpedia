-- Prove2me | Theorems.Thm_BandParity_val_two_mul_of_lt
-- name    : BandParity.val_two_mul_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:01:06.730157+00:00
-- url     : https://prove2.me/theorems/b63927fd-25a5-5d09-8b98-1367dc1593de
-- title:
--   Band Parity: val two mul of lt
-- statement:
--   The Band Parity construction uses the val two mul of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L59-L61
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L59-L61

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

theorem BandParity.val_two_mul_of_lt (hp2 : p ≠ 2) {x : ZMod p} (hx : 2 * x.val < p) :
    (2 * x).val = 2 * x.val := by sorry
