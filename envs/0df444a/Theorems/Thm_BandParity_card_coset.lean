-- Prove2me | Theorems.Thm_BandParity_card_coset
-- name    : BandParity.card_coset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:54:04.822559+00:00
-- url     : https://prove2.me/theorems/4fc09738-6c3e-46e7-88f8-3a808d1b37b6
-- title:
--   Band Parity: card coset
-- statement:
--   The Band Parity construction uses the card coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/OddSubgroup.lean#L166-L173
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/OddSubgroup.lean#L166-L173

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
omit hN hN3 hH

theorem BandParity.card_coset (x : (ZMod N)ˣ) : (coset H x).card = Nat.card H := by sorry
