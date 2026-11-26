-- Prove2me | Theorems.Thm_BandParity_bandSum_im
-- name    : BandParity.bandSum_im
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:13:37.997685+00:00
-- url     : https://prove2.me/theorems/e4f676a6-1598-4969-bafe-68916fd4bb34
-- title:
--   Band Parity: band Sum im
-- statement:
--   **Coset form, imaginary part.** `e = ∑_{u ∈ C_i} s(u) s(u²)`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/Solution.lean#L76-L78
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/Solution.lean#L76-L78

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

theorem BandParity.bandSum_im (hp8 : p % 8 = 5) :
    (bandSum χ).im = ∑ u ∈ cls χ gi, parSign u * parSign (u ^ 2) := by sorry
