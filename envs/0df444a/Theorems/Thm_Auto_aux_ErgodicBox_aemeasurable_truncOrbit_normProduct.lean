-- Prove2me | Theorems.Thm_Auto_aux_ErgodicBox_aemeasurable_truncOrbit_normProduct
-- name    : Auto.aux_ErgodicBox.aemeasurable_truncOrbit_normProduct
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T17:44:41.164796+00:00
-- url     : https://prove2.me/theorems/a2d48282-22d4-5bb0-ad01-d58a14b5984e
-- title:
--   aux Ergodic Box: aemeasurable trunc Orbit norm Product
-- statement:
--   Measurability of the discrete norm product for finite orbit truncations.
--   The pointwise norm formula is the same one used in the finite-box Hölder
--   estimate.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2807-L2828
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2807-L2828

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

theorem Auto.aux_ErgodicBox.aemeasurable_truncOrbit_normProduct
    {X κ : Type*} [MeasurableSpace X] [MeasurableSpace κ]
    [Countable κ] [MeasurableSingletonClass κ] {μ : Measure X}
    {n : ℕ} (B : Finset κ) (T : κ → X → X)
    (hT : ∀ k ∈ B, MeasurePreserving (T k) μ μ)
    (f : Fin n → X → ℝ) (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (p : Fin n → ℝ≥0∞) (hp0 : ∀ i, p i ≠ 0) (hptop : ∀ i, p i ≠ ∞)
    (hpreal : ∀ i, 0 < (p i).toReal) :
    AEMeasurable (fun x ↦
      ∏ i, eLpNorm (truncOrbit B T (f i) x) (p i) Measure.count ^ 2) μ := by sorry
