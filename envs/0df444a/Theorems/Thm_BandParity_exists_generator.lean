-- Prove2me | Theorems.Thm_BandParity_exists_generator
-- name    : BandParity.exists_generator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:51:29.554549+00:00
-- url     : https://prove2.me/theorems/c79ae0ca-53fd-49f6-af0e-30b613c126f8
-- title:
--   Band Parity: exists generator
-- statement:
--   A generator of `(ZMod p)ˣ`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean#L83-L88
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean#L83-L88

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

theorem BandParity.exists_generator :
    ∃ g : (ZMod p)ˣ, orderOf g = p - 1 ∧ ∀ u : (ZMod p)ˣ, ∃ k : ℕ, g ^ k = u := by sorry
