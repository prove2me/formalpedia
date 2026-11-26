-- Prove2me | Theorems.Thm_BandParity_lag_identity
-- name    : BandParity.lag_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:13:47.762066+00:00
-- url     : https://prove2.me/theorems/09ed5f05-706b-42ce-a653-0fb2d203affa
-- title:
--   Band Parity: lag identity
-- statement:
--   **The lag identity.** `∑_{u ∈ C_i} s(u) s(2u) = κ`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/Solution.lean#L81-L83
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/Solution.lean#L81-L83

module
public import Definitions.Def_BandParity
public import Definitions.Def_BandParity_Solution
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ

theorem BandParity.lag_identity (hp8 : p % 8 = 5) :
    ∑ u ∈ cls χ gi, parSign u * parSign (2 * u) = kappa p := by sorry
