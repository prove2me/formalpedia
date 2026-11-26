-- Prove2me | Theorems.Thm_Auto_aux_ErgodicBox_holder_truncOrbit_norms
-- name    : Auto.aux_ErgodicBox.holder_truncOrbit_norms
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:44:27.129402+00:00
-- url     : https://prove2.me/theorems/c723c81f-6e86-4706-b2df-c2e99899c01d
-- title:
--   aux Ergodic Box: holder trunc Orbit norms
-- statement:
--   The aux Ergodic Box construction uses the holder trunc Orbit norms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2612-L2663
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2612-L2663

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

theorem Auto.aux_ErgodicBox.holder_truncOrbit_norms
    {X κ : Type*} [MeasurableSpace X] [MeasurableSpace κ]
    [Countable κ] [MeasurableSingletonClass κ] {μ : Measure X}
    {n : ℕ} (B : Finset κ) (T : κ → X → X)
    (hT : ∀ k ∈ B, MeasurePreserving (T k) μ μ)
    (f : Fin n → X → ℝ) (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (p : Fin n → ℝ≥0∞) (hp0 : ∀ i, p i ≠ 0) (hptop : ∀ i, p i ≠ ∞)
    (hpreal : ∀ i, 0 < (p i).toReal)
    (hqsum : ∑ i, 2 / (p i).toReal = 1) :
    ∫⁻ x, ∏ i, eLpNorm (truncOrbit B T (f i) x) (p i) Measure.count ^ 2 ∂μ ≤
      B.card * ∏ i, eLpNorm (f i) (p i) μ ^ 2 := by sorry
