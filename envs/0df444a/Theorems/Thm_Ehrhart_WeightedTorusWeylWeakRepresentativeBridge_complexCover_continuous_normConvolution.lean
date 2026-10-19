-- Prove2me | Theorems.Thm_Ehrhart_WeightedTorusWeylWeakRepresentativeBridge_complexCover_continuous_normConvolution
-- name    : Ehrhart.WeightedTorusWeylWeakRepresentativeBridge.complexCover_continuous_normConvolution
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:53.846488+00:00
-- url     : https://prove2.me/theorems/bcec9f25-1b79-4d58-a91e-7fb989720981
-- title:
--   Ehrhart.WeightedTorusWeylWeakRepresentativeBridge.complexCover_continuous_normConvolution
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
open Ehrhart.WeightedTorusWeylWeakRepresentativeBridge
open Set Function MeasureTheory Filter
open scoped BigOperators ContDiff Convolution ENNReal InnerProductSpace Topology
open WeightedBrascampSaturation DolbeaultRegularity ComplexKillingSaturationBridge
open DolbeaultGraphDistributionBridge WeightedTorusDistributionBridge
open WeightedTorusClosedGraphWeakBridge WeightedTorusWeylRepresentativeBridge
open WeightedTorusWeylRadialIntegrationBridge

theorem Ehrhart.WeightedTorusWeylWeakRepresentativeBridge.complexCover_continuous_normConvolution {n : ℕ}
    {κ η : TorusCharacters.LogSpace n → ℝ}
    (hκcont : Continuous κ) (hκcompact : HasCompactSupport κ)
    (hηcont : Continuous η) (hηcompact : HasCompactSupport η) :
    Continuous
      ((fun z => ‖κ z‖)
        ⋆[ContinuousLinearMap.mul ℝ ℝ,
          (volume : Measure (TorusCharacters.LogSpace n))]
            (fun z => ‖η z‖)) := by sorry
