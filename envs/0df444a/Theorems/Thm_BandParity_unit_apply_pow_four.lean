-- Prove2me | Theorems.Thm_BandParity_unit_apply_pow_four
-- name    : BandParity.unit_apply_pow_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:51:30.711923+00:00
-- url     : https://prove2.me/theorems/b64c5948-fccf-454a-ab0c-de83e796bbfc
-- title:
--   Band Parity: unit apply pow four
-- statement:
--   The Band Parity construction uses the unit apply pow four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean#L90-L92
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean#L90-L92

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_BandParity_Basic
set_option autoImplicit true
@[expose] public section
public section
open BandParity
variable {p : ℕ} [hp : Fact p.Prime]

theorem BandParity.unit_apply_pow_four {R : Type*} [CommRing R] (χ : MulChar (ZMod p) R) (hχ : orderOf χ = 4)
    (u : (ZMod p)ˣ) : χ u ^ 4 = 1 := by sorry
