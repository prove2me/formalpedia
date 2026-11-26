-- Prove2me | Theorems.Thm_BandParity_sum_uSign
-- name    : BandParity.sum_uSign
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:54:12.584925+00:00
-- url     : https://prove2.me/theorems/7b896e4f-89f3-47ed-8d95-5eadd781acb5
-- title:
--   Band Parity: sum u Sign
-- statement:
--   The Band Parity construction uses the sum u Sign property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/OddSubgroup.lean#L176-L189
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/OddSubgroup.lean#L176-L189

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
omit [NeZero N] hN hN3 hH

theorem BandParity.sum_uSign (S : Finset (ZMod N)ˣ) :
    ∑ u ∈ S, uSign u = (S.card : ℤ) - 2 * oddCount S := by sorry
