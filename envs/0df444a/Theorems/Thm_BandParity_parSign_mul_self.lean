-- Prove2me | Theorems.Thm_BandParity_parSign_mul_self
-- name    : BandParity.parSign_mul_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:02:29.969822+00:00
-- url     : https://prove2.me/theorems/8e755f9a-fc9a-4b48-a80e-22a1968d8763
-- title:
--   Band Parity: par Sign mul self
-- statement:
--   The Band Parity construction uses the par Sign mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L37-L38
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L37-L38

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

theorem BandParity.parSign_mul_self (x : ZMod p) : parSign x * parSign x = 1 := by sorry
