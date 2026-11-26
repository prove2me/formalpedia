-- Prove2me | Theorems.Thm_BandParity_apply_neg_one_of_odd_orderOf
-- name    : BandParity.apply_neg_one_of_odd_orderOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:53:29.164679+00:00
-- url     : https://prove2.me/theorems/3fdb4237-c444-58a9-afce-ed5699ac04ef
-- title:
--   Band Parity: apply neg one of odd order Of
-- statement:
--   **Proposition 1.1, odd orders.** A character of odd order is even.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean#L95-L103
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean#L95-L103

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

theorem BandParity.apply_neg_one_of_odd_orderOf {R : Type*} [CommRing R] (χ : MulChar (ZMod p) R)
    (h : Odd (orderOf χ)) : χ (-1) = 1 := by sorry
