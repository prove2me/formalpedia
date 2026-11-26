-- Prove2me | Theorems.Thm_BandParity_sum_legendre_even_half
-- name    : BandParity.sum_legendre_even_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:06:48.461799+00:00
-- url     : https://prove2.me/theorems/e5af40d7-1777-4ceb-9382-efc85bd11d42
-- title:
--   Band Parity: sum legendre even half
-- statement:
--   `∑_{0 < v < p/2, v even} (v/p) = (2/p) κ`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L71-L83
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Main.lean#L71-L83

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem BandParity.sum_legendre_even_half :
    ∑ v ∈ (range p).filter (fun v => 0 < v ∧ 2 * v < p ∧ v % 2 = 0), legendreSym p (v : ℤ) =
      legendreSym p 2 * kappa p := by sorry
