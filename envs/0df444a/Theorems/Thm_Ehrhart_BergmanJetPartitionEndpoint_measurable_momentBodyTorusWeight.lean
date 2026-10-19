-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetPartitionEndpoint_measurable_momentBodyTorusWeight
-- name    : Ehrhart.BergmanJetPartitionEndpoint.measurable_momentBodyTorusWeight
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:00.136627+00:00
-- url     : https://prove2.me/theorems/5962cf03-b4c1-4dcb-819d-22c899a151e7
-- title:
--   Ehrhart.BergmanJetPartitionEndpoint.measurable_momentBodyTorusWeight
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
open Ehrhart.BergmanJetPartitionEndpoint
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert MomentOptimizer MomentTargetGeodesic MomentTargetDanskin
open MomentFirstVariation MomentRegularity BergmanJetTorusEnvelope BergmanJetTorusCoercivity
open JetEnvelopeSlopeConvergence JetEnvelopeRightDerivative LogPartitionConvexity
open scoped BigOperators ENNReal Topology

theorem Ehrhart.BergmanJetPartitionEndpoint.measurable_momentBodyTorusWeight
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) :
    Measurable (momentBodyTorusWeight K p t) := by sorry
