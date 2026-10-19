-- Prove2me | Theorems.Thm_Ehrhart_ArbitraryBodyOneSidedAngularResolventDefect_mem_sourceFreeAngularWeightedMeanZeroSubmodule_iff
-- name    : Ehrhart.ArbitraryBodyOneSidedAngularResolventDefect.mem_sourceFreeAngularWeightedMeanZeroSubmodule_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:58.667884+00:00
-- url     : https://prove2.me/theorems/e76c67dc-00e2-4c56-883a-e0441ef300f4
-- title:
--   Ehrhart.ArbitraryBodyOneSidedAngularResolventDefect.mem_sourceFreeAngularWeightedMeanZeroSubmodule_iff
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

theorem Ehrhart.ArbitraryBodyOneSidedAngularResolventDefect.mem_sourceFreeAngularWeightedMeanZeroSubmodule_iff
    {n : ℕ} (a : LogTorus n → ℝ)
    [IsFiniteMeasure (angularWeightedTorusMeasure a)]
    (f : angularWeightedScalarL2 a) :
    f ∈ sourceFreeAngularWeightedMeanZeroSubmodule a ↔
      (∫ q : LogTorus n,
        f q ∂(angularWeightedTorusMeasure a)) = 0 := by sorry
