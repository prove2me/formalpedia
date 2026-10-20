-- Prove2me | Theorems.Thm_Ehrhart_WeightedTorusWeylWeakRepresentativeBridge_complexCover_locallyIntegrable_norm
-- name    : Ehrhart.WeightedTorusWeylWeakRepresentativeBridge.complexCover_locallyIntegrable_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:53.846488+00:00
-- url     : https://prove2.me/theorems/ed3cd387-ef80-4b0f-abd4-323a38682aef
-- title:
--   Ehrhart.WeightedTorusWeylWeakRepresentativeBridge.complexCover_locallyIntegrable_norm
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

theorem Ehrhart.WeightedTorusWeylWeakRepresentativeBridge.complexCover_locallyIntegrable_norm {n : ℕ}
    {g : TorusCharacters.LogSpace n → ℂ}
    (hg : LocallyIntegrable g
      (volume : Measure (TorusCharacters.LogSpace n))) :
    LocallyIntegrable (fun z => ‖g z‖)
      (volume : Measure (TorusCharacters.LogSpace n)) := by sorry
