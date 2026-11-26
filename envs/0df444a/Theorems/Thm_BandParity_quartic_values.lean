-- Prove2me | Theorems.Thm_BandParity_quartic_values
-- name    : BandParity.quartic_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:54:07.755331+00:00
-- url     : https://prove2.me/theorems/f2e432ad-a850-4ce5-aeda-cd56b7fe335f
-- title:
--   Band Parity: quartic values
-- statement:
--   Nonzero values of a quartic character are fourth roots of unity.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean#L123-L125
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean#L123-L125

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

theorem BandParity.quartic_values {a : ZMod p} (ha : a ≠ 0) :
    χ a = 1 ∨ χ a = gi ∨ χ a = -1 ∨ χ a = -gi := by sorry
