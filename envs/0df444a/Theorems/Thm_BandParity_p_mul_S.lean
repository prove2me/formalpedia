-- Prove2me | Theorems.Thm_BandParity_p_mul_S
-- name    : BandParity.p_mul_S
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:54:47.533676+00:00
-- url     : https://prove2.me/theorems/959e9543-2b13-4e0c-9d45-516720461e91
-- title:
--   Band Parity: p mul S
-- statement:
--   The Band Parity construction uses the p mul S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L85-L86
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L85-L86

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

theorem BandParity.p_mul_S (hp5 : 5 < p) (z : GaussianInt) : (p : ℤ) * S χ z = cosetSum χ z := by sorry
