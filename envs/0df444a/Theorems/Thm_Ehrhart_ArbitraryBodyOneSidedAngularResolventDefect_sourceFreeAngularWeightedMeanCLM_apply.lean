-- Prove2me | Theorems.Thm_Ehrhart_ArbitraryBodyOneSidedAngularResolventDefect_sourceFreeAngularWeightedMeanCLM_apply
-- name    : Ehrhart.ArbitraryBodyOneSidedAngularResolventDefect.sourceFreeAngularWeightedMeanCLM_apply
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:58.667884+00:00
-- url     : https://prove2.me/theorems/ae79a240-ba9b-4b2c-8451-f5720567693d
-- title:
--   Ehrhart.ArbitraryBodyOneSidedAngularResolventDefect.sourceFreeAngularWeightedMeanCLM_apply
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

theorem Ehrhart.ArbitraryBodyOneSidedAngularResolventDefect.sourceFreeAngularWeightedMeanCLM_apply
    {n : ℕ} (a : LogTorus n → ℝ)
    [IsFiniteMeasure (angularWeightedTorusMeasure a)]
    (f : angularWeightedScalarL2 a) :
    sourceFreeAngularWeightedMeanCLM a f =
      ∫ q : LogTorus n, f q ∂(angularWeightedTorusMeasure a) := by sorry
