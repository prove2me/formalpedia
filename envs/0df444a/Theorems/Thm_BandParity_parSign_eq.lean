-- Prove2me | Theorems.Thm_BandParity_parSign_eq
-- name    : BandParity.parSign_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:01:40.871016+00:00
-- url     : https://prove2.me/theorems/67904172-290a-4459-a0a4-f9290a5af40f
-- title:
--   Band Parity: par Sign eq
-- statement:
--   The Band Parity construction uses the par Sign eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L33-L34
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L33-L34

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
omit hp

theorem BandParity.parSign_eq (x : ZMod p) : parSign x = 1 ∨ parSign x = -1 := by sorry
