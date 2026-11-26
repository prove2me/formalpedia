-- Prove2me | Theorems.Thm_BandParity_quartic_apply_two
-- name    : BandParity.quartic_apply_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:52:22.089562+00:00
-- url     : https://prove2.me/theorems/2442aa5f-7fea-4526-8537-09f4028162aa
-- title:
--   Band Parity: quartic apply two
-- statement:
--   For `p ≡ 5 (mod 8)`, `χ 2 = ± i`: `2` is a quadratic non-residue.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean#L207-L211
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean#L207-L211

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
variable (χ : MulChar (ZMod p) GaussianInt) (hχ : orderOf χ = 4)
include hχ

theorem BandParity.quartic_apply_two (hp8 : p % 8 = 5) : χ 2 = gi ∨ χ 2 = -gi := by sorry
