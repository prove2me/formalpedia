-- Prove2me | Theorems.Thm_BandParity_bandSum_eq
-- name    : BandParity.bandSum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:00:56.63516+00:00
-- url     : https://prove2.me/theorems/ed8890db-7adf-5909-838f-63b8a246db22
-- title:
--   Band Parity: band Sum eq
-- statement:
--   **Coset form of `𝒞(p)`.** `𝒞 = ∑_{C₁} s(u)s(u²) + i ∑_{C_i} s(u)s(u²)`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L241-L262
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L241-L262

module
public import Definitions.Def_BandParity_Defs
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_Laws
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ

theorem BandParity.bandSum_eq (hp8 : p % 8 = 5) :
    bandSum χ = ((∑ u ∈ cls χ 1, parSign u * parSign (u ^ 2) : ℤ) : GaussianInt)
      + gi * ((∑ u ∈ cls χ gi, parSign u * parSign (u ^ 2) : ℤ) : GaussianInt) := by sorry
