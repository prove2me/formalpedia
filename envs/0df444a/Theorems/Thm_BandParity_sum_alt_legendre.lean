-- Prove2me | Theorems.Thm_BandParity_sum_alt_legendre
-- name    : BandParity.sum_alt_legendre
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:06:21.797364+00:00
-- url     : https://prove2.me/theorems/43924a59-edaa-5503-acc2-92772870a65a
-- title:
--   Band Parity: sum alt legendre
-- statement:
--   `∑_{0 < v < p/2} (-1)^v (v/p) = -2κ` for `p ≡ 5 (mod 8)`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L86-L110
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L86-L110

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem BandParity.sum_alt_legendre (hp8 : p % 8 = 5) :
    ∑ v ∈ (range p).filter (fun v => 0 < v ∧ 2 * v < p), (-1 : ℤ) ^ v * legendreSym p (v : ℤ) =
      -2 * kappa p := by sorry
