-- Prove2me | Theorems.Thm_BandParity_uSign_neg
-- name    : BandParity.uSign_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:53:48.347515+00:00
-- url     : https://prove2.me/theorems/eb62a526-d855-5928-9002-0eab8a71e3e1
-- title:
--   Band Parity: u Sign neg
-- statement:
--   The Band Parity construction uses the u Sign neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/OddSubgroup.lean#L67-L74
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/OddSubgroup.lean#L67-L74

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

theorem BandParity.uSign_neg (u : (ZMod N)ˣ) : uSign (-u) = -uSign u := by sorry
