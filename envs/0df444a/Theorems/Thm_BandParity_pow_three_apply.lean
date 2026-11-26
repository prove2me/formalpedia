-- Prove2me | Theorems.Thm_BandParity_pow_three_apply
-- name    : BandParity.pow_three_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:55:24.087333+00:00
-- url     : https://prove2.me/theorems/1cadc5ff-3758-4ca1-bb45-6e0e84cd81df
-- title:
--   Band Parity: pow three apply
-- statement:
--   The conjugate character `χ ^ 3` is `star ∘ χ`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L217-L221
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L217-L221

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

theorem BandParity.pow_three_apply (n : ZMod p) : (χ ^ 3) n = star (χ n) := by sorry
