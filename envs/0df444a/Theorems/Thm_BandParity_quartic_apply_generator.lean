-- Prove2me | Theorems.Thm_BandParity_quartic_apply_generator
-- name    : BandParity.quartic_apply_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:51:26.156427+00:00
-- url     : https://prove2.me/theorems/331a1ac0-4bd1-545a-a1a7-122dde3912b0
-- title:
--   Band Parity: quartic apply generator
-- statement:
--   On a generator, a quartic character takes the value `± i`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean#L128-L143
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean#L128-L143

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

theorem BandParity.quartic_apply_generator {g : (ZMod p)ˣ} (hg : ∀ u : (ZMod p)ˣ, ∃ k : ℕ, g ^ k = u) :
    χ g = gi ∨ χ g = -gi := by sorry
