-- Prove2me | Theorems.Thm_BandParity_bandSignPow_eq
-- name    : BandParity.bandSignPow_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:53:47.420707+00:00
-- url     : https://prove2.me/theorems/0b4b762d-fad8-560b-b319-27530704fdae
-- title:
--   Band Parity: band Sign Pow eq
-- statement:
--   **Parity dictionary.** `ε(u) = s(u) s(u^e)` for `e ≥ 1`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/OddSubgroup.lean#L78-L96
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/OddSubgroup.lean#L78-L96

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
omit hN3

theorem BandParity.bandSignPow_eq {e : ℕ} (he0 : e ≠ 0) (u : (ZMod N)ˣ) :
    bandSignPow e u = uSign u * uSign (u ^ e) := by sorry
