-- Prove2me | Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_weightedScalarFundamentalLiftLI_ae_eq
-- name    : Ehrhart.WeightedTorusClosedGraphWeakBridge.weightedScalarFundamentalLiftLI_ae_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:52.714743+00:00
-- url     : https://prove2.me/theorems/15325f2f-82ce-4d5b-acff-df8cd5959a3c
-- title:
--   Ehrhart.WeightedTorusClosedGraphWeakBridge.weightedScalarFundamentalLiftLI_ae_eq
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
open Ehrhart.WeightedTorusClosedGraphWeakBridge
open Set Function MeasureTheory Filter
open WeightedTorusHilbert WeightedBrascampSaturation ComplexKillingSaturationBridge
open DolbeaultGraphDistributionBridge WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
  Manifold ContDiff

theorem Ehrhart.WeightedTorusClosedGraphWeakBridge.weightedScalarFundamentalLiftLI_ae_eq {n k : ℕ}
    (φ : Space n → ℝ) (b : Space n)
    (f : weightedTorusScalarL2 k φ) :
    (fun p : Space n × Space n =>
      weightedScalarFundamentalLiftLI k φ b f p) =ᵐ[
        realWeightedFundamentalCellMeasure k φ b]
      (fun p => f (realTorusCoverProjection n p)) := by sorry
