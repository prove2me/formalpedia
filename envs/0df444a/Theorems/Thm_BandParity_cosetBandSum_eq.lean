-- Prove2me | Theorems.Thm_BandParity_cosetBandSum_eq
-- name    : BandParity.cosetBandSum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:14:38.031673+00:00
-- url     : https://prove2.me/theorems/b8bedfac-0db6-4795-b4df-0eeb8a4c0304
-- title:
--   Band Parity: coset Band Sum eq
-- statement:
--   **Representative identity.** `T^{(e)}_{H,x}(N) = ∑_{u ∈ xH} s(u) s(u^e)` for even `e ≥ 2`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/Solution.lean#L123-L125
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/Solution.lean#L123-L125

module
public import Definitions.Def_BandParity
public import Definitions.Def_BandParity_Solution
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {N : ℕ} [NeZero N] (hN : Odd N) (hN3 : 3 ≤ N)
variable {H : Subgroup (ZMod N)ˣ} [DecidablePred (· ∈ H)] (hH : Odd (Nat.card H))
include hN hN3 hH

theorem BandParity.cosetBandSum_eq (x : (ZMod N)ˣ) {e : ℕ} (he : Even e) (he0 : e ≠ 0) :
    cosetBandSum H x e = ∑ u ∈ coset H x, uSign u * uSign (u ^ e) := by sorry
