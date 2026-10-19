-- Prove2me | Theorems.Thm_Ehrhart_TorusWeightedAdjointMollification_finite_complex_local_square_integral_sum_tendsto_zero
-- name    : Ehrhart.TorusWeightedAdjointMollification.finite_complex_local_square_integral_sum_tendsto_zero
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:03.298759+00:00
-- url     : https://prove2.me/theorems/f0cd6d60-88d1-4b54-8179-3a39c3c81f75
-- title:
--   Ehrhart.TorusWeightedAdjointMollification.finite_complex_local_square_integral_sum_tendsto_zero
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | EhrhartVolumeInequality | external Lean 4.33.1 validation; bundle SHA256 7150ea60aef8441515028279454832b05d0f964f3966505d147b2c1d8afe9763

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusWeightedAdjointMollification
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert WeightedTorusDistributionBridge
open WeightedDolbeaultBochnerIdentity WeightedTorusDolbeault TorusWeakDolbeaultMollification
open TorusFriedrichsMollifierEstimates TorusMollifiedBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution

theorem Ehrhart.TorusWeightedAdjointMollification.finite_complex_local_square_integral_sum_tendsto_zero
    {n : ℕ} {ι : Type*}
    (s : Finset ι)
    (g : ι → ℕ → LogSpace n → ℂ)
    {K : Set (LogSpace n)} (hK : IsCompact K)
    (hcontinuous : ∀ i ∈ s, ∀ k : ℕ, Continuous (g i k))
    (hvanish : ∀ i ∈ s,
      Tendsto
        (fun k : ℕ =>
          ∫ x in K, ‖g i k x‖ ^ 2
            ∂(volume : Measure (LogSpace n)))
        atTop (nhds 0)) :
    Tendsto
      (fun k : ℕ =>
        ∫ x in K, ‖∑ i ∈ s, g i k x‖ ^ 2
          ∂(volume : Measure (LogSpace n)))
      atTop (nhds 0) := by sorry
