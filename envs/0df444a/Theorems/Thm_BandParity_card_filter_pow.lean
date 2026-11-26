-- Prove2me | Theorems.Thm_BandParity_card_filter_pow
-- name    : BandParity.card_filter_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:54:28.284848+00:00
-- url     : https://prove2.me/theorems/60814995-11fd-426e-8682-fe100186e9a0
-- title:
--   Band Parity: card filter pow
-- statement:
--   Counting through the power map: `#{u ∈ X : P(u^e)} = d · #{y ∈ X^e : P y}`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/OddSubgroup.lean#L229-L247
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/OddSubgroup.lean#L229-L247

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

theorem BandParity.card_filter_pow (x : (ZMod N)ˣ) (e : ℕ) (P : (ZMod N)ˣ → Prop) [DecidablePred P] :
    ((coset H x).filter (fun u => P (u ^ e))).card =
      (powKer H e).card * (((coset H x).image (· ^ e)).filter P).card := by sorry
