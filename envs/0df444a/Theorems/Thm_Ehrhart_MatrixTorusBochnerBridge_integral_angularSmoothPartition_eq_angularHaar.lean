-- Prove2me | Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_integral_angularSmoothPartition_eq_angularHaar
-- name    : Ehrhart.MatrixTorusBochnerBridge.integral_angularSmoothPartition_eq_angularHaar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:55.424275+00:00
-- url     : https://prove2.me/theorems/fa74ea39-300d-4f72-bbe0-fae1f9551791
-- title:
--   Ehrhart.MatrixTorusBochnerBridge.integral_angularSmoothPartition_eq_angularHaar
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

theorem Ehrhart.MatrixTorusBochnerBridge.integral_angularSmoothPartition_eq_angularHaar
    {n : ℕ}
    {g : TorusCharacters.AngularTorus n → ℂ}
    (hg : Continuous g) :
    (∫ t : Space n,
      (angularSmoothPartition t : ℂ) *
        g (angularCoverProjection n t)
      ∂(volume : Measure (Space n))) =
      ∫ θ : TorusCharacters.AngularTorus n,
        g θ ∂(angularMeasure n) := by sorry
