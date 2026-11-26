-- Prove2me | Theorems.Thm_Auto_aux_ErgodicBox_realErgodicAverage_sub_aestronglyMeasurable
-- name    : Auto.aux_ErgodicBox.realErgodicAverage_sub_aestronglyMeasurable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T17:45:07.424204+00:00
-- url     : https://prove2.me/theorems/e8a9a937-5be2-5673-ba71-e5371e5e6e2c
-- title:
--   aux Ergodic Box: real Ergodic Average sub aestrongly Measurable
-- statement:
--   The aux Ergodic Box construction uses the real Ergodic Average sub aestrongly Measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2974-L2981
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L2974-L2981

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

theorem Auto.aux_ErgodicBox.realErgodicAverage_sub_aestronglyMeasurable {X : Type*}
    [MeasurableSpace X] {μ : Measure X} {n : ℕ}
    (S : ErgodicSystem X μ n) (N M : ℕ) (f : Fin n → X → ℝ)
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun x ↦ realErgodicAverage S N f x -
      realErgodicAverage S M f x) μ := by sorry
