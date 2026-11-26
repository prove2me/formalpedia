-- Prove2me | Theorems.Thm_Auto_aux_floor_intCast_add_of_mem_Ico
-- name    : Auto.aux_floor_intCast_add_of_mem_Ico
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:36:59.95067+00:00
-- url     : https://prove2.me/theorems/f077028f-b741-4d22-84e2-26e586506ab7
-- title:
--   Auto: aux floor int Cast add of mem Ico
-- statement:
--   The Auto construction uses the aux floor int Cast add of mem Ico property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L429-L436
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L429-L436

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

theorem Auto.aux_floor_intCast_add_of_mem_Ico (z : ℤ) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ⌊(z : ℝ) + r⌋ = z := by sorry
