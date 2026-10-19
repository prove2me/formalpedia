-- Prove2me | Theorems.Thm_Ehrhart_ArbitraryBodyOneSidedAngularWeightedKernel_smoothConvexPotential_upper_of_support_upper
-- name    : Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel.smoothConvexPotential_upper_of_support_upper
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:58.667884+00:00
-- url     : https://prove2.me/theorems/6eb83278-5b3e-4a02-a3ff-1549b11f202d
-- title:
--   Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel.smoothConvexPotential_upper_of_support_upper
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

theorem Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel.smoothConvexPotential_upper_of_support_upper
    {n : ℕ} (K : CenteredBody n)
    {a : LogTorus n → ℝ} {C : ℝ}
    (hupper : ∀ q : LogTorus n,
      a q ≤ SupportFunction.supportFunction
        K.carrier q.1 + C)
    (q : LogTorus n) :
    a q ≤ smoothConvexPotential K q.1 + (C + 1) := by sorry
