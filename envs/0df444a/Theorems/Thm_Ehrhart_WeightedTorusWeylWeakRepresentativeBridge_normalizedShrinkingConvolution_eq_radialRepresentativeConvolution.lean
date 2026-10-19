-- Prove2me | Theorems.Thm_Ehrhart_WeightedTorusWeylWeakRepresentativeBridge_normalizedShrinkingConvolution_eq_radialRepresentativeConvolution
-- name    : Ehrhart.WeightedTorusWeylWeakRepresentativeBridge.normalizedShrinkingConvolution_eq_radialRepresentativeConvolution
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:55.424275+00:00
-- url     : https://prove2.me/theorems/c390d4d0-36e3-4273-bc7d-fc386e21d147
-- title:
--   Ehrhart.WeightedTorusWeylWeakRepresentativeBridge.normalizedShrinkingConvolution_eq_radialRepresentativeConvolution
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

theorem Ehrhart.WeightedTorusWeylWeakRepresentativeBridge.normalizedShrinkingConvolution_eq_radialRepresentativeConvolution
    {n : ℕ}
    {g : TorusCharacters.LogSpace n → ℂ}
    (hg : LocallyIntegrable g
      (volume : Measure (TorusCharacters.LogSpace n)))
    (hweak : (∀ weakTest, ContDiff ℝ 1 weakTest → HasCompactSupport weakTest →
      ∀ weakCoordinate,
        (∫ weakPoint, g weakPoint *
          coverBarPartialTest weakTest weakCoordinate weakPoint) = 0))
    (m : ℕ) (z : TorusCharacters.LogSpace n) :
    (((complexShrinkingBump (n := n) m).normed
        (volume : Measure (TorusCharacters.LogSpace n)))
      ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
        (volume : Measure (TorusCharacters.LogSpace n))] g) z =
      (((complexShrinkingBump (n := n) m).normed
          (volume : Measure (TorusCharacters.LogSpace n)))
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
          (volume : Measure (TorusCharacters.LogSpace n))]
            productRadialHolomorphicMollification g) z := by sorry
