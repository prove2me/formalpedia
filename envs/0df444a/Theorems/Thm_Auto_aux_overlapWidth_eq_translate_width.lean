-- Prove2me | Theorems.Thm_Auto_aux_overlapWidth_eq_translate_width
-- name    : Auto.aux_overlapWidth_eq_translate_width
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:40:02.11894+00:00
-- url     : https://prove2.me/theorems/b1f72a9e-2036-4f41-94aa-8260a5624f52
-- title:
--   Auto: aux overlap Width eq translate width
-- statement:
--   The Auto construction uses the aux overlap Width eq translate width property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L771-L776
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L771-L776

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section

theorem Auto.aux_overlapWidth_eq_translate_width {n : ℕ} (hn : 0 < n)
    (ε δ : ℝ) (u : aux_RVector n) (m : ℕ) :
    aux_overlapWidth hn ε δ u =
      aux_overlapUpper hn ε δ u m - aux_overlapLower hn ε u m := by sorry
