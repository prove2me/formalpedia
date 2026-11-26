-- Prove2me | Theorems.Thm_BandParity_neg_one_ne_one
-- name    : BandParity.neg_one_ne_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:51:55.535113+00:00
-- url     : https://prove2.me/theorems/dad8178f-485e-4acb-a186-29833acea5a5
-- title:
--   Band Parity: neg one ne one
-- statement:
--   The Band Parity construction uses the neg one ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean#L40-L41
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean#L40-L41

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_BandParity_Basic
set_option autoImplicit true
@[expose] public section
public section
open BandParity

theorem BandParity.neg_one_ne_one : (-1 : GaussianInt) ≠ 1 := by sorry
