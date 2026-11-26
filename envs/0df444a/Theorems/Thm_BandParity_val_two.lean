-- Prove2me | Theorems.Thm_BandParity_val_two
-- name    : BandParity.val_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:01:07.356011+00:00
-- url     : https://prove2.me/theorems/3c197d77-ff04-4142-b539-62c7637a14de
-- title:
--   Band Parity: val two
-- statement:
--   The Band Parity construction uses the val two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L51-L54
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L51-L54

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

theorem BandParity.val_two (hp2 : p ≠ 2) : (2 : ZMod p).val = 2 := by sorry
