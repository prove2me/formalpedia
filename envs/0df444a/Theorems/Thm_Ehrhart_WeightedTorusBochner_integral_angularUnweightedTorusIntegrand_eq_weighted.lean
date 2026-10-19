-- Prove2me | Theorems.Thm_Ehrhart_WeightedTorusBochner_integral_angularUnweightedTorusIntegrand_eq_weighted
-- name    : Ehrhart.WeightedTorusBochner.integral_angularUnweightedTorusIntegrand_eq_weighted
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:57.23131+00:00
-- url     : https://prove2.me/theorems/d97de837-4cb7-4ce6-86bf-4b820230656c
-- title:
--   Ehrhart.WeightedTorusBochner.integral_angularUnweightedTorusIntegrand_eq_weighted
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
open Ehrhart.WeightedTorusBochner
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert JetEnvelopeSlopeConvergence EqualitySaturatingKillingPaths
open ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity WeightedTorusDistributionBridge
open WeightedTorusGraphWeakBridge MatrixTorusBochnerBridge MatrixTorusBochnerIdentity
open WeightedTorusDolbeault
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff

theorem Ehrhart.WeightedTorusBochner.integral_angularUnweightedTorusIntegrand_eq_weighted
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (f : LogTorus n → ℂ) :
    (∫ p : LogTorus n,
      angularUnweightedTorusIntegrand a f p
        ∂(sourceTorusBaseMeasure n)) =
      ∫ p : LogTorus n, f p ∂(angularWeightedTorusMeasure a) := by sorry
