-- Prove2me | Theorems.Thm_BandParity_parSign_two_mul_of_lt
-- name    : BandParity.parSign_two_mul_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:02:32.945122+00:00
-- url     : https://prove2.me/theorems/4b7b6915-8717-5443-aec1-0d54b6282900
-- title:
--   Band Parity: par Sign two mul of lt
-- statement:
--   The Band Parity construction uses the par Sign two mul of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L63-L65
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L63-L65

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

theorem BandParity.parSign_two_mul_of_lt (hp2 : p ≠ 2) {x : ZMod p} (hx : 2 * x.val < p) :
    parSign (2 * x) = 1 := by sorry
