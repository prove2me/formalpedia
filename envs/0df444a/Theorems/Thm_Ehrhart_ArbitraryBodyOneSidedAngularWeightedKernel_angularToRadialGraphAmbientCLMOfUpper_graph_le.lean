-- Prove2me | Theorems.Thm_Ehrhart_ArbitraryBodyOneSidedAngularWeightedKernel_angularToRadialGraphAmbientCLMOfUpper_graph_le
-- name    : Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel.angularToRadialGraphAmbientCLMOfUpper_graph_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:58.667884+00:00
-- url     : https://prove2.me/theorems/ab253a7a-eb9f-42b5-90e3-452283b87518
-- title:
--   Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel.angularToRadialGraphAmbientCLMOfUpper_graph_le
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
open Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert WeightedBrascampSaturation JetEnvelopeSlopeConvergence
open ComplexKillingSaturationBridge WeightedTorusDolbeault WeightedTorusBrascampLieb
open ArbitraryBodySmoothConvexPotentialBridge
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff

theorem Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel.angularToRadialGraphAmbientCLMOfUpper_graph_le
    {n : ℕ} {a : LogTorus n → ℝ}
    {φ : Space n → ℝ} {C : ℝ}
    (hφ : Continuous φ)
    (hupper : ∀ q : LogTorus n, a q ≤ φ q.1 + C) :
    (angularDolbeaultGraph a).map
      (angularToRadialGraphAmbientCLMOfUpper hφ hupper).toLinearMap ≤
        functionDolbeaultGraph 1 φ := by sorry
