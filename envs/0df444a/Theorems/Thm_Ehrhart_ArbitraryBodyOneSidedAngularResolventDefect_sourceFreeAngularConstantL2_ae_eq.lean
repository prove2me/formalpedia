-- Prove2me | Theorems.Thm_Ehrhart_ArbitraryBodyOneSidedAngularResolventDefect_sourceFreeAngularConstantL2_ae_eq
-- name    : Ehrhart.ArbitraryBodyOneSidedAngularResolventDefect.sourceFreeAngularConstantL2_ae_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:58.667884+00:00
-- url     : https://prove2.me/theorems/e6d2235d-7cb7-4f7b-a902-4bf795de6173
-- title:
--   Ehrhart.ArbitraryBodyOneSidedAngularResolventDefect.sourceFreeAngularConstantL2_ae_eq
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
open Ehrhart.ArbitraryBodyOneSidedAngularResolventDefect
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert JetEnvelopeSlopeConvergence LogPartitionConvexity WeightedTorusDolbeault
open WeightedTorusBrascampLieb ArbitraryBodyOneSidedAngularWeightedKernel
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff

theorem Ehrhart.ArbitraryBodyOneSidedAngularResolventDefect.sourceFreeAngularConstantL2_ae_eq
    {n : ℕ} (a : LogTorus n → ℝ)
    [IsFiniteMeasure (angularWeightedTorusMeasure a)]
    (c : ℂ) :
    (fun q : LogTorus n => sourceFreeAngularConstantL2 a c q) =ᵐ[
      angularWeightedTorusMeasure a] (fun _ => c) := by sorry
