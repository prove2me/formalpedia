-- Prove2me | Theorems.Thm_Ehrhart_ArbitraryBodyOneSidedAngularWeightedKernel_angularZeroGraph_ae_constant_of_support_upper
-- name    : Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel.angularZeroGraph_ae_constant_of_support_upper
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:58.667884+00:00
-- url     : https://prove2.me/theorems/afff881a-f92c-419a-8ceb-fcdc90e7c712
-- title:
--   Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel.angularZeroGraph_ae_constant_of_support_upper
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

theorem Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel.angularZeroGraph_ae_constant_of_support_upper
    {n : ℕ} (K : CenteredBody n)
    {a : LogTorus n → ℝ} (ha : Continuous a)
    {C : ℝ}
    (hupper : ∀ q : LogTorus n,
      a q ≤ SupportFunction.supportFunction
        K.carrier q.1 + C)
    (f : angularWeightedScalarL2 a)
    (hf : WithLp.toLp 2
      (f, (0 : angularWeightedFormL2 a)) ∈
        angularDolbeaultGraph a) :
    ∃ c : ℂ,
      (fun q : LogTorus n => f q) =ᵐ[
        angularWeightedTorusMeasure a]
          (fun _ => c) := by sorry
