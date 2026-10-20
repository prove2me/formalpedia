-- Prove2me | Theorems.Thm_Ehrhart_WeightedTorusBrascampLieb_angularWeakScalarResolventCLM_selfAdjoint
-- name    : Ehrhart.WeightedTorusBrascampLieb.angularWeakScalarResolventCLM_selfAdjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:58.667884+00:00
-- url     : https://prove2.me/theorems/e37e805f-7ef3-418a-a5f9-22c9762295be
-- title:
--   Ehrhart.WeightedTorusBrascampLieb.angularWeakScalarResolventCLM_selfAdjoint
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
open Ehrhart.WeightedTorusBrascampLieb
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert WeightedBrascampSaturation ComplexKillingSaturationBridge
open ComplexSaturatedKillingFieldBridge WeightedTorusWeylWeakRepresentativeBridge
open JointHolomorphicLaurentFourierCompatibility WeightedTorusDolbeault WeightedTorusBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff

theorem Ehrhart.WeightedTorusBrascampLieb.angularWeakScalarResolventCLM_selfAdjoint {n : ℕ}
    (a : LogTorus n → ℝ) (f g : angularWeightedScalarL2 a) :
    @inner ℂ (angularWeightedScalarL2 a) _
      (angularWeakScalarResolventCLM a f) g =
      @inner ℂ (angularWeightedScalarL2 a) _ f
        (angularWeakScalarResolventCLM a g) := by sorry
