-- Prove2me | Theorems.Thm_Ehrhart_WeightedTorusWeylRadialIntegrationBridge_radialPolarIntegrand_integrableOn_compactDomain
-- name    : Ehrhart.WeightedTorusWeylRadialIntegrationBridge.radialPolarIntegrand_integrableOn_compactDomain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:53.846488+00:00
-- url     : https://prove2.me/theorems/07c40f8f-32b2-4241-9c8e-c573c2746aab
-- title:
--   Ehrhart.WeightedTorusWeylRadialIntegrationBridge.radialPolarIntegrand_integrableOn_compactDomain
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

theorem Ehrhart.WeightedTorusWeylRadialIntegrationBridge.radialPolarIntegrand_integrableOn_compactDomain
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) :
    IntegrableOn (radialPolarIntegrand f c)
      compactPolarDomain (volume : Measure (ℝ × ℝ)) := by sorry
