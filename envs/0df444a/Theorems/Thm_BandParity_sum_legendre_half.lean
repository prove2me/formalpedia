-- Prove2me | Theorems.Thm_BandParity_sum_legendre_half
-- name    : BandParity.sum_legendre_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:06:35.048019+00:00
-- url     : https://prove2.me/theorems/be3b9ebd-65fb-4ef8-b849-61eb9a40532d
-- title:
--   Band Parity: sum legendre half
-- statement:
--   `∑_{0 < v < p/2} (v/p) = 0` for `p ≡ 1 (mod 4)`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L58-L68
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L58-L68

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem BandParity.sum_legendre_half (hp4 : p % 4 = 1) :
    ∑ v ∈ (range p).filter (fun v => 0 < v ∧ 2 * v < p), legendreSym p (v : ℤ) = 0 := by sorry
