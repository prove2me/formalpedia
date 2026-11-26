-- Prove2me | Theorems.Thm_BandParity_not_both
-- name    : BandParity.not_both
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:53:50.507183+00:00
-- url     : https://prove2.me/theorems/240f5f4a-9545-50f5-84d3-b284a4d6d43b
-- title:
--   Band Parity: not both
-- statement:
--   The Band Parity construction uses the not both property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/OddSubgroup.lean#L115-L119
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/OddSubgroup.lean#L115-L119

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

theorem BandParity.not_both (x u : (ZMod N)ˣ) : ¬ (x⁻¹ * u ∈ H ∧ -(x⁻¹ * u) ∈ H) := by sorry
