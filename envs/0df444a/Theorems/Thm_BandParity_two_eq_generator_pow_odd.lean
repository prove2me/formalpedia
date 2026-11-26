-- Prove2me | Theorems.Thm_BandParity_two_eq_generator_pow_odd
-- name    : BandParity.two_eq_generator_pow_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:51:48.376658+00:00
-- url     : https://prove2.me/theorems/8d4aa90c-e69b-5785-b7ca-6f915cad6065
-- title:
--   Band Parity: two eq generator pow odd
-- statement:
--   `2` is an odd power of any generator when `p ≡ 5 (mod 8)`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean#L187-L204
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean#L187-L204

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

theorem BandParity.two_eq_generator_pow_odd (hp8 : p % 8 = 5) {g : (ZMod p)ˣ}
    (hg : ∀ u : (ZMod p)ˣ, ∃ k : ℕ, g ^ k = u) :
    ∃ e : ℕ, Odd e ∧ ((g ^ e : (ZMod p)ˣ) : ZMod p) = 2 := by sorry
