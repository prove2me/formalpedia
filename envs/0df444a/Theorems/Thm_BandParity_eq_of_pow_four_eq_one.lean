-- Prove2me | Theorems.Thm_BandParity_eq_of_pow_four_eq_one
-- name    : BandParity.eq_of_pow_four_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:51:28.002476+00:00
-- url     : https://prove2.me/theorems/b4f849de-d8c7-5828-b776-08b5bff97f0c
-- title:
--   Band Parity: eq of pow four eq one
-- statement:
--   The fourth roots of unity in `ℤ[i]` are `1, i, -1, -i`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean#L44-L54
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean#L44-L54

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_BandParity_Basic
set_option autoImplicit true
@[expose] public section
public section
open BandParity

theorem BandParity.eq_of_pow_four_eq_one {x : GaussianInt} (h : x ^ 4 = 1) :
    x = 1 ∨ x = gi ∨ x = -1 ∨ x = -gi := by sorry
