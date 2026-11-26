-- Prove2me | Theorems.Thm_BandParity_parSign_neg
-- name    : BandParity.parSign_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:01:22.022964+00:00
-- url     : https://prove2.me/theorems/95c39500-55e8-4403-8820-1d4e793db3cd
-- title:
--   Band Parity: par Sign neg
-- statement:
--   The Band Parity construction uses the par Sign neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L42-L49
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L42-L49

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

theorem BandParity.parSign_neg (hp2 : p ≠ 2) {x : ZMod p} (hx : x ≠ 0) : parSign (-x) = -parSign x := by sorry
