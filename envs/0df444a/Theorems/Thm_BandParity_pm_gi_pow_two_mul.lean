-- Prove2me | Theorems.Thm_BandParity_pm_gi_pow_two_mul
-- name    : BandParity.pm_gi_pow_two_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:51:30.69855+00:00
-- url     : https://prove2.me/theorems/c91b74f6-e052-429b-aa1b-b3f3691e8eca
-- title:
--   Band Parity: pm gi pow two mul
-- statement:
--   Even powers of `± i` are `(-1) ^ j`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean#L66-L69
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean#L66-L69

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_BandParity_Basic
set_option autoImplicit true
@[expose] public section
public section
open BandParity

theorem BandParity.pm_gi_pow_two_mul {u : GaussianInt} (hu : u = gi ∨ u = -gi) (j : ℕ) :
    u ^ (2 * j) = (-1) ^ j := by sorry
