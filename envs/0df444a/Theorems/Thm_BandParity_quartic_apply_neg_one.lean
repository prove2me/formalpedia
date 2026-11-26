-- Prove2me | Theorems.Thm_BandParity_quartic_apply_neg_one
-- name    : BandParity.quartic_apply_neg_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:54:17.99492+00:00
-- url     : https://prove2.me/theorems/d3be29b4-f57d-44fa-a8d9-7a6db669ce5a
-- title:
--   Band Parity: quartic apply neg one
-- statement:
--   **Proposition 1.1, order four.** For `p ≡ 5 (mod 8)` a quartic character is odd.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean#L168-L174
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean#L168-L174

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

theorem BandParity.quartic_apply_neg_one (hp8 : p % 8 = 5) : χ (-1) = -1 := by sorry
