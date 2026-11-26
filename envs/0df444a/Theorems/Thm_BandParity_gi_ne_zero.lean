-- Prove2me | Theorems.Thm_BandParity_gi_ne_zero
-- name    : BandParity.gi_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:01:10.342802+00:00
-- url     : https://prove2.me/theorems/6d285f08-c2ad-480e-aa9f-84ab99607c36
-- title:
--   Band Parity: gi ne zero
-- statement:
--   The Band Parity construction uses the gi ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L163-L163
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L163-L163

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

theorem BandParity.gi_ne_zero : gi ≠ 0 := by sorry
