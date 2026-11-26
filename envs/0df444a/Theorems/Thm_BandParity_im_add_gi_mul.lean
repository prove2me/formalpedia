-- Prove2me | Theorems.Thm_BandParity_im_add_gi_mul
-- name    : BandParity.im_add_gi_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:02:36.763923+00:00
-- url     : https://prove2.me/theorems/bbe1e5e2-cf0c-4de2-88c1-93f515d18ce7
-- title:
--   Band Parity: im add gi mul
-- statement:
--   The Band Parity construction uses the im add gi mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L238-L238
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L238-L238

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

theorem BandParity.im_add_gi_mul (a b : ℤ) : ((a : GaussianInt) + gi * b).im = b := by sorry
