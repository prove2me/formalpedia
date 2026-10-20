-- Prove2me | Theorems.Thm_Ehrhart_ArbitraryBodyOneSidedAngularWeightedKernel_angularToRadialLpOfUpper_ae_eq
-- name    : Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel.angularToRadialLpOfUpper_ae_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:58.667884+00:00
-- url     : https://prove2.me/theorems/28582e13-17e9-46bf-a6d4-98c0d856b2cf
-- title:
--   Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel.angularToRadialLpOfUpper_ae_eq
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

theorem Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel.angularToRadialLpOfUpper_ae_eq
    {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {a : LogTorus n → ℝ}
    {φ : Space n → ℝ} {C : ℝ}
    (hφ : Continuous φ)
    (hupper : ∀ q : LogTorus n, a q ≤ φ q.1 + C)
    (f : MeasureTheory.Lp E 2 (angularWeightedTorusMeasure a)) :
    (fun q => angularToRadialLpOfUpper hφ hupper f q) =ᵐ[
      weightedTorusMeasure 1 φ] (fun q => f q) := by sorry
