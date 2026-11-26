-- Prove2me | Theorems.Thm_BandParity_ringChar_ne_two
-- name    : BandParity.ringChar_ne_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:05:19.755714+00:00
-- url     : https://prove2.me/theorems/2facd82a-f4dc-4c69-9261-a272ad933b89
-- title:
--   Band Parity: ring Char ne two
-- statement:
--   The Band Parity construction uses the ring Char ne two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L44-L45
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L44-L45

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem BandParity.ringChar_ne_two (hp2 : p ≠ 2) : ringChar (ZMod p) ≠ 2 := by sorry
