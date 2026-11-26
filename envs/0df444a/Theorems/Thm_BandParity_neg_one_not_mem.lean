-- Prove2me | Theorems.Thm_BandParity_neg_one_not_mem
-- name    : BandParity.neg_one_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:53:45.586934+00:00
-- url     : https://prove2.me/theorems/79fc9061-5ea9-5b47-9ba8-94f6478e0b07
-- title:
--   Band Parity: neg one not mem
-- statement:
--   The Band Parity construction uses the neg one not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/OddSubgroup.lean#L102-L112
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/OddSubgroup.lean#L102-L112

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
omit [NeZero N] hN [DecidablePred (· ∈ H)]

theorem BandParity.neg_one_not_mem : (-1 : (ZMod N)ˣ) ∉ H := by sorry
