-- Prove2me | Theorems.Thm_Ehrhart_TorusDeckWeightedUnfolding_exists_finite_complex_fundamental_test_partition
-- name    : Ehrhart.TorusDeckWeightedUnfolding.exists_finite_complex_fundamental_test_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:01.857667+00:00
-- url     : https://prove2.me/theorems/e2855772-efb0-412d-9c12-323f00990b42
-- title:
--   Ehrhart.TorusDeckWeightedUnfolding.exists_finite_complex_fundamental_test_partition
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
open Ehrhart.TorusDeckWeightedUnfolding
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence
open WeightedTorusDistributionBridge WeightedTorusClosedGraphWeakBridge WeightedTorusDolbeault
open WeightedTorusBochner TorusWeightedBaseAE
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution Manifold

theorem Ehrhart.TorusDeckWeightedUnfolding.exists_finite_complex_fundamental_test_partition
    {n : ℕ}
    {ψ : LogSpace n → ℂ}
    (hψcompact : HasCompactSupport ψ) :
    ∃ (s : Finset (LogSpace n))
      (χ : LogSpace n → LogSpace n → ℝ),
      (∀ i, ContDiff ℝ ∞ (χ i)) ∧
      (∀ i, tsupport (χ i) ⊆
        coverFundamentalInterior (coverCenteredFundamentalBase i)) ∧
      (∀ z : LogSpace n,
        ψ z = ∑ i ∈ s, (χ i z : ℂ) * ψ z) := by sorry
