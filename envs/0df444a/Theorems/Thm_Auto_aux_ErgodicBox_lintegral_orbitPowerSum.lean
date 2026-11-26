-- Prove2me | Theorems.Thm_Auto_aux_ErgodicBox_lintegral_orbitPowerSum
-- name    : Auto.aux_ErgodicBox.lintegral_orbitPowerSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:44:09.643196+00:00
-- url     : https://prove2.me/theorems/dc933f43-3ab4-43b7-abd6-e19653a986b6
-- title:
--   aux Ergodic Box: lintegral orbit Power Sum
-- statement:
--   The aux Ergodic Box construction uses the lintegral orbit Power Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2510-L2530
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2510-L2530

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

theorem Auto.aux_ErgodicBox.lintegral_orbitPowerSum
    {X κ : Type*} [MeasurableSpace X] {μ : Measure X}
    (B : Finset κ) (T : κ → X → X)
    (hT : ∀ k ∈ B, MeasurePreserving (T k) μ μ)
    (f : X → ℝ) (hf : AEStronglyMeasurable f μ) (p : ℝ) :
    ∫⁻ x, orbitPowerSum B T f p x ∂μ =
      B.card * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by sorry
