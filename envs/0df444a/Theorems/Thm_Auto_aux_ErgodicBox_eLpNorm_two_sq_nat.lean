-- Prove2me | Theorems.Thm_Auto_aux_ErgodicBox_eLpNorm_two_sq_nat
-- name    : Auto.aux_ErgodicBox.eLpNorm_two_sq_nat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:38:43.282823+00:00
-- url     : https://prove2.me/theorems/4a549dd0-0966-5619-9977-e1b5698d950b
-- title:
--   aux Ergodic Box: e Lp Norm two sq nat
-- statement:
--   The aux Ergodic Box construction uses the e Lp Norm two sq nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2665-L2672
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2665-L2672

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
open Auto.aux_ErgodicBox
open MeasureTheory Set
open scoped ENNReal BigOperators

theorem Auto.aux_ErgodicBox.eLpNorm_two_sq_nat {α E : Type*} [MeasurableSpace α]
    [TopologicalSpace E] [ENorm E] (μ : Measure α) (f : α → E) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) ∂μ := by sorry
