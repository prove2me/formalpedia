-- Prove2me | Theorems.Thm_BandParity_gi_ne_neg_gi
-- name    : BandParity.gi_ne_neg_gi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:51:54.395155+00:00
-- url     : https://prove2.me/theorems/8b4c2d73-4f59-4fbf-9989-3826dfd89570
-- title:
--   Band Parity: gi ne neg gi
-- statement:
--   The Band Parity construction uses the gi ne neg gi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean#L37-L38
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Basic.lean#L37-L38

module
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import Definitions.Def_BandParity_Basic
set_option autoImplicit true
@[expose] public section
public section
open BandParity

theorem BandParity.gi_ne_neg_gi : gi ≠ -gi := by sorry
