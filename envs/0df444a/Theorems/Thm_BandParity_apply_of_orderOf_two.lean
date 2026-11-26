-- Prove2me | Theorems.Thm_BandParity_apply_of_orderOf_two
-- name    : BandParity.apply_of_orderOf_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:53:32.532891+00:00
-- url     : https://prove2.me/theorems/bba9ba45-2bce-4943-9fb4-b96981a5dd5f
-- title:
--   Band Parity: apply of order Of two
-- statement:
--   **Proposition 1.1, order two.** A character of order two is real: its values are
--   `0` and `± 1`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean#L107-L115
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean#L107-L115

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

theorem BandParity.apply_of_orderOf_two (χ : MulChar (ZMod p) GaussianInt) (hχ : orderOf χ = 2)
    (a : ZMod p) : χ a = 0 ∨ χ a = 1 ∨ χ a = -1 := by sorry
