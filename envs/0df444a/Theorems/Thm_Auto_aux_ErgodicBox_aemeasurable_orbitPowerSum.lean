-- Prove2me | Theorems.Thm_Auto_aux_ErgodicBox_aemeasurable_orbitPowerSum
-- name    : Auto.aux_ErgodicBox.aemeasurable_orbitPowerSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:38:39.635822+00:00
-- url     : https://prove2.me/theorems/59802460-a09f-465d-b627-c7e4c8a239a4
-- title:
--   aux Ergodic Box: aemeasurable orbit Power Sum
-- statement:
--   The aux Ergodic Box construction uses the aemeasurable orbit Power Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2499-L2508
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2499-L2508

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

theorem Auto.aux_ErgodicBox.aemeasurable_orbitPowerSum
    {X κ : Type*} [MeasurableSpace X] {μ : Measure X}
    (B : Finset κ) (T : κ → X → X)
    (hT : ∀ k ∈ B, MeasurePreserving (T k) μ μ)
    (f : X → ℝ) (hf : AEStronglyMeasurable f μ) (p : ℝ) :
    AEMeasurable (orbitPowerSum B T f p) μ := by sorry
