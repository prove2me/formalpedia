-- Prove2me | Theorems.Thm_BandParity_pm_gi_pow_odd
-- name    : BandParity.pm_gi_pow_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:51:39.259893+00:00
-- url     : https://prove2.me/theorems/a75d6797-1c34-4045-ad23-fcac771a6b88
-- title:
--   Band Parity: pm gi pow odd
-- statement:
--   Odd powers of `± i` are `± i`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean#L57-L63
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean#L57-L63

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_BandParity_Basic
set_option autoImplicit true
@[expose] public section
public section
open BandParity

theorem BandParity.pm_gi_pow_odd {u : GaussianInt} (hu : u = gi ∨ u = -gi) {e : ℕ} (he : Odd e) :
    u ^ e = gi ∨ u ^ e = -gi := by sorry
