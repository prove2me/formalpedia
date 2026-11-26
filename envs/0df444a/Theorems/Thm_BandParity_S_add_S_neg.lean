-- Prove2me | Theorems.Thm_BandParity_S_add_S_neg
-- name    : BandParity.S_add_S_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:54:44.254198+00:00
-- url     : https://prove2.me/theorems/840f5ce1-0180-5e19-8f97-3296313ce69b
-- title:
--   Band Parity: S add S neg
-- statement:
--   **Proposition 3.1 (pairing).** `S_z + S_{-z} = (p - 1)/4`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L170-L182
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L170-L182

module
public import Definitions.Def_BandParity_Pin
public import Definitions.Def_BandParity_FixedBase
public import Definitions.Def_BandParity_CosetSums
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ

theorem BandParity.S_add_S_neg (hp8 : p % 8 = 5) (hp5 : 5 < p) (z : GaussianInt)
    (hz : z = 1 ∨ z = gi ∨ z = -1 ∨ z = -gi) :
    S χ z + S χ (-z) = ((p - 1) / 4 : ℕ) := by sorry
