-- Prove2me | Theorems.Thm_BandParity_unit_val_ne_zero
-- name    : BandParity.unit_val_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:53:52.104962+00:00
-- url     : https://prove2.me/theorems/7ec3ebac-3fe9-423c-88ca-0f4212f70a1f
-- title:
--   Band Parity: unit val ne zero
-- statement:
--   The Band Parity construction uses the unit val ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/OddSubgroup.lean#L63-L65
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/OddSubgroup.lean#L63-L65

module
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_OddSubgroup
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {N : ℕ} [NeZero N]
variable (hN : Odd N) (hN3 : 3 ≤ N)
include hN hN3
omit [NeZero N] hN

theorem BandParity.unit_val_ne_zero (u : (ZMod N)ˣ) : (u : ZMod N).val ≠ 0 := by sorry
