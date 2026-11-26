-- Prove2me | Theorems.Thm_BandParity_odd_card_powKer
-- name    : BandParity.odd_card_powKer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:54:19.899062+00:00
-- url     : https://prove2.me/theorems/f7f3b092-d742-483f-9d47-eef142f56251
-- title:
--   Band Parity: odd card pow Ker
-- statement:
--   The Band Parity construction uses the odd card pow Ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/OddSubgroup.lean#L196-L205
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/OddSubgroup.lean#L196-L205

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
variable {H : Subgroup (ZMod N)ˣ} [DecidablePred (· ∈ H)] (hH : Odd (Nat.card H))
include hH
omit hN hN3

theorem BandParity.odd_card_powKer (e : ℕ) : Odd (powKer H e).card := by sorry
