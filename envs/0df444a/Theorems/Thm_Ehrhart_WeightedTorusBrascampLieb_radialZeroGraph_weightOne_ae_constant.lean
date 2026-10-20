-- Prove2me | Theorems.Thm_Ehrhart_WeightedTorusBrascampLieb_radialZeroGraph_weightOne_ae_constant
-- name    : Ehrhart.WeightedTorusBrascampLieb.radialZeroGraph_weightOne_ae_constant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:58.667884+00:00
-- url     : https://prove2.me/theorems/06ee0c8c-6db9-4749-a071-7a5458be1f66
-- title:
--   Ehrhart.WeightedTorusBrascampLieb.radialZeroGraph_weightOne_ae_constant
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

theorem Ehrhart.WeightedTorusBrascampLieb.radialZeroGraph_weightOne_ae_constant
    {n : ℕ} (K : CenteredBody n)
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {B : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction
        K.carrier x| ≤ B)
    (f : weightedTorusScalarL2 1 φ)
    (hf : WithLp.toLp 2
      (f, (0 : weightedTorusFormL2 1 φ)) ∈
        functionDolbeaultGraph 1 φ) :
    ∃ c : ℂ, (fun q : LogTorus n => f q) =ᵐ[
      weightedTorusMeasure 1 φ] (fun _ => c) := by sorry
