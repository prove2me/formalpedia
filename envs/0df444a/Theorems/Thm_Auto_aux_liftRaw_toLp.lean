-- Prove2me | Theorems.Thm_Auto_aux_liftRaw_toLp
-- name    : Auto.aux_liftRaw_toLp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:36:24.702246+00:00
-- url     : https://prove2.me/theorems/cb02c9ab-b24a-5694-ac52-34c5c8534885
-- title:
--   Auto: aux lift Raw to Lp
-- statement:
--   The Auto construction uses the aux lift Raw to Lp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L630-L633
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L630-L633

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

theorem Auto.aux_liftRaw_toLp {n : ℕ} (F : aux_RVector n → ℝ)
    (x : aux_RVector n) :
    aux_liftRaw F (WithLp.toLp 2 x) = F x := by sorry
