-- Prove2me | Theorems.Thm_BandParity_card_fibre
-- name    : BandParity.card_fibre
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:54:23.444972+00:00
-- url     : https://prove2.me/theorems/86f5c23b-7fea-4b62-bc56-ccedd5e20029
-- title:
--   Band Parity: card fibre
-- statement:
--   Every fibre of `u ↦ u^e` on `xH` has the size of the kernel.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/OddSubgroup.lean#L209-L225
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/OddSubgroup.lean#L209-L225

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

theorem BandParity.card_fibre (x : (ZMod N)ˣ) (e : ℕ) {u₀ : (ZMod N)ˣ} (hu₀ : u₀ ∈ coset H x) :
    ((coset H x).filter (fun u => u ^ e = u₀ ^ e)).card = (powKer H e).card := by sorry
