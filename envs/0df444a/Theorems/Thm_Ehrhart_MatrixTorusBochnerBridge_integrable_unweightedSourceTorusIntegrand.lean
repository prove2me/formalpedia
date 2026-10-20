-- Prove2me | Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_integrable_unweightedSourceTorusIntegrand
-- name    : Ehrhart.MatrixTorusBochnerBridge.integrable_unweightedSourceTorusIntegrand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:55.424275+00:00
-- url     : https://prove2.me/theorems/8a01a538-f8cb-4a59-a1cb-10dba583a442
-- title:
--   Ehrhart.MatrixTorusBochnerBridge.integrable_unweightedSourceTorusIntegrand
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

theorem Ehrhart.MatrixTorusBochnerBridge.integrable_unweightedSourceTorusIntegrand
    {n : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    Integrable (unweightedSourceTorusIntegrand φ f)
      ((volume : Measure (Space n)).prod
        (angularMeasure n)) := by sorry
