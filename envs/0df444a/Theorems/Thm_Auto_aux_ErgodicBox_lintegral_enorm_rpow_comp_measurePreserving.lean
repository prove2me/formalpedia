-- Prove2me | Theorems.Thm_Auto_aux_ErgodicBox_lintegral_enorm_rpow_comp_measurePreserving
-- name    : Auto.aux_ErgodicBox.lintegral_enorm_rpow_comp_measurePreserving
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:43:56.037803+00:00
-- url     : https://prove2.me/theorems/b4aec348-052e-4f0f-a913-bbd44c82a938
-- title:
--   aux Ergodic Box: lintegral enorm rpow comp measure Preserving
-- statement:
--   The aux Ergodic Box construction uses the lintegral enorm rpow comp measure Preserving property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2485-L2493
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2485-L2493

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

theorem Auto.aux_ErgodicBox.lintegral_enorm_rpow_comp_measurePreserving
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (T : X → X) (hT : MeasurePreserving T μ μ)
    (f : X → ℝ) (hf : AEStronglyMeasurable f μ) (p : ℝ) :
    ∫⁻ x, ‖f (T x)‖ₑ ^ p ∂μ = ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by sorry
