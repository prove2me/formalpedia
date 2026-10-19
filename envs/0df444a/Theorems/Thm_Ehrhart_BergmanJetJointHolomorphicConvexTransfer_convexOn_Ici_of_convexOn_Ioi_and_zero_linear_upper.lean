-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicConvexTransfer_convexOn_Ici_of_convexOn_Ioi_and_zero_linear_upper
-- name    : Ehrhart.BergmanJetJointHolomorphicConvexTransfer.convexOn_Ici_of_convexOn_Ioi_and_zero_linear_upper
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:09.94113+00:00
-- url     : https://prove2.me/theorems/f4f037e3-588f-4a57-bb7d-32d16fb679cd
-- title:
--   Ehrhart.BergmanJetJointHolomorphicConvexTransfer.convexOn_Ici_of_convexOn_Ioi_and_zero_linear_upper
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
open Ehrhart.BergmanJetJointHolomorphicConvexTransfer
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert MomentOptimizer MomentTargetGeodesic MomentFirstVariation
open MomentRegularity BergmanJetTorusEnvelope BergmanJetPartitionEndpoint
open BergmanJetJointHolomorphicStrictSchur BergmanJetJointHolomorphicPhysicalApproximation
open JetEnvelopeSlopeConvergence LogPartitionConvexity
open scoped BigOperators ENNReal Topology

theorem Ehrhart.BergmanJetJointHolomorphicConvexTransfer.convexOn_Ici_of_convexOn_Ioi_and_zero_linear_upper
    (f : ℝ → ℝ) (C : ℝ)
    (hfzero : f 0 = 0)
    (hfconv : ConvexOn ℝ (Set.Ioi 0) f)
    (hupper : ∀ t : ℝ, 0 < t → f t ≤ C * t) :
    ConvexOn ℝ (Set.Ici 0) f := by sorry
