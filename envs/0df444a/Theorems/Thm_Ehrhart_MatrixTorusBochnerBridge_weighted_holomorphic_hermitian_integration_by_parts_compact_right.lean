-- Prove2me | Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_weighted_holomorphic_hermitian_integration_by_parts_compact_right
-- name    : Ehrhart.MatrixTorusBochnerBridge.weighted_holomorphic_hermitian_integration_by_parts_compact_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:55.424275+00:00
-- url     : https://prove2.me/theorems/3aa4ced3-3648-46fa-889d-6b0fb003390f
-- title:
--   Ehrhart.MatrixTorusBochnerBridge.weighted_holomorphic_hermitian_integration_by_parts_compact_right
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
open Ehrhart.MatrixTorusBochnerBridge
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert EqualitySaturatingKillingPaths WeightedTorusDistributionBridge
open WeightedDolbeaultBochnerIdentity
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff

theorem Ehrhart.MatrixTorusBochnerBridge.weighted_holomorphic_hermitian_integration_by_parts_compact_right
    {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    {F G : TorusCharacters.LogSpace n → ℂ}
    (ha : ContDiff ℝ 1 a)
    (hF : ContDiff ℝ 1 F)
    (hG : ContDiff ℝ 1 G)
    (hGcompact : HasCompactSupport G)
    (j : Fin n) :
    (∫ z : TorusCharacters.LogSpace n,
      weightedHolomorphicDerivative a F j z * conj (G z)
      ∂(coverWeightedMeasure a)) =
    -(∫ z : TorusCharacters.LogSpace n,
      F z * conj (barPartialCoordinate G z j)
      ∂(coverWeightedMeasure a)) := by sorry
