-- Prove2me | Theorems.Thm_BandParity_re_add_gi_mul
-- name    : BandParity.re_add_gi_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:02:02.601395+00:00
-- url     : https://prove2.me/theorems/894866b1-491b-5d1e-889a-9e2d858c2b16
-- title:
--   Band Parity: re add gi mul
-- statement:
--   The Band Parity construction uses the re add gi mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L235-L235
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L235-L235

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
omit hp hχ

theorem BandParity.re_add_gi_mul (a b : ℤ) : ((a : GaussianInt) + gi * b).re = a := by sorry
