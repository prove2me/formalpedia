-- Prove2me | Theorems.Thm_Ehrhart_WeightedTorusWeylRadialIntegrationBridge_integrable_productRadialWeightedIntegrand
-- name    : Ehrhart.WeightedTorusWeylRadialIntegrationBridge.integrable_productRadialWeightedIntegrand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:53.846488+00:00
-- url     : https://prove2.me/theorems/de03044a-00da-4c3a-905b-9c158a01d2d1
-- title:
--   Ehrhart.WeightedTorusWeylRadialIntegrationBridge.integrable_productRadialWeightedIntegrand
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
open Ehrhart.WeightedTorusWeylRadialIntegrationBridge
open Set MeasureTheory Filter Complex
open scoped BigOperators ContDiff Convolution ENNReal Topology
open WeightedTorusWeylRepresentativeBridge

theorem Ehrhart.WeightedTorusWeylRadialIntegrationBridge.integrable_productRadialWeightedIntegrand {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Continuous F) :
    Integrable (productRadialWeightedIntegrand F)
      (volume : Measure
        (TorusCharacters.LogSpace n)) := by sorry
