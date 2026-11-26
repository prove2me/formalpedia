-- Prove2me | Theorems.Thm_Auto_aux_ErgodicBox_aemeasurable_enorm_rpow
-- name    : Auto.aux_ErgodicBox.aemeasurable_enorm_rpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:36:28.409973+00:00
-- url     : https://prove2.me/theorems/0c57d921-daaa-457d-8341-c3419e4b24d6
-- title:
--   aux Ergodic Box: aemeasurable enorm rpow
-- statement:
--   The aux Ergodic Box construction uses the aemeasurable enorm rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2480-L2483
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2480-L2483

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

theorem Auto.aux_ErgodicBox.aemeasurable_enorm_rpow {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (f : X → ℝ) (hf : AEStronglyMeasurable f μ) (p : ℝ) :
    AEMeasurable (fun x ↦ ‖f x‖ₑ ^ p) μ := by sorry
