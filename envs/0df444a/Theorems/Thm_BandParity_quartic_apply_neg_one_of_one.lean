-- Prove2me | Theorems.Thm_BandParity_quartic_apply_neg_one_of_one
-- name    : BandParity.quartic_apply_neg_one_of_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:54:29.117037+00:00
-- url     : https://prove2.me/theorems/b9993222-f4f3-465c-9892-d718a8ffe840
-- title:
--   Band Parity: quartic apply neg one of one
-- statement:
--   **Proposition 1.1, order four, converse.** For `p ≡ 1 (mod 8)` a quartic character is even.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean#L177-L183
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean#L177-L183

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

theorem BandParity.quartic_apply_neg_one_of_one (hp8 : p % 8 = 1) : χ (-1) = 1 := by sorry
