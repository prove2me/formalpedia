-- Prove2me | Theorems.Thm_BandParity_cosetSum_pow_three
-- name    : BandParity.cosetSum_pow_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:54:53.091871+00:00
-- url     : https://prove2.me/theorems/a82aaecb-976a-4205-a41b-91b94465e96b
-- title:
--   Band Parity: coset Sum pow three
-- statement:
--   The Band Parity construction uses the coset Sum pow three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L223-L227
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/CosetSums.lean#L223-L227

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

theorem BandParity.cosetSum_pow_three (z : GaussianInt) : cosetSum (χ ^ 3) z = cosetSum χ (star z) := by sorry
