-- Prove2me | Theorems.Thm_BandParity_neg_one_eq_generator_pow
-- name    : BandParity.neg_one_eq_generator_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:51:33.525415+00:00
-- url     : https://prove2.me/theorems/6966f76c-3798-4d24-9226-03c7b5857eae
-- title:
--   Band Parity: neg one eq generator pow
-- statement:
--   `-1 = g ^ ((p - 1) / 2)` for a generator `g`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean#L147-L165
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean#L147-L165

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
omit hχ

theorem BandParity.neg_one_eq_generator_pow (hp2 : p ≠ 2) {g : (ZMod p)ˣ} (hgo : orderOf g = p - 1) :
    ((g ^ ((p - 1) / 2) : (ZMod p)ˣ) : ZMod p) = -1 := by sorry
