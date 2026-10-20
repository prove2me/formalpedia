-- Prove2me | Theorems.Thm_Ehrhart_RadialAccelerationBounds_hasCompactSupport_sourceJointTrueRadialTimeKernel
-- name    : Ehrhart.RadialAccelerationBounds.hasCompactSupport_sourceJointTrueRadialTimeKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:00.136627+00:00
-- url     : https://prove2.me/theorems/024747c3-9894-4f6f-8d5a-1158010dc8bc
-- title:
--   Ehrhart.RadialAccelerationBounds.hasCompactSupport_sourceJointTrueRadialTimeKernel
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
open Ehrhart.RadialAccelerationBounds
open Set Filter Function MeasureTheory
open JetEnvelopeGlobalPlurisubharmonic EnvelopeTorusDescent EnvelopeGeneralTorusDescent
open JetEnvelopeTrueRadialMollifier
open scoped Topology ENNReal Convolution ContDiff
attribute [local instance] Ehrhart.RadialAccelerationBounds.sourceJointCoverVolume_isAddHaar

theorem Ehrhart.RadialAccelerationBounds.hasCompactSupport_sourceJointTrueRadialTimeKernel (n k : ℕ) :
    HasCompactSupport (sourceJointTrueRadialTimeKernel n k) := by sorry
