-- Prove2me | Theorems.Thm_Ehrhart_JetEnvelopeGlobalPlurisubharmonic_jointLogTime_sourceJointPhaseHomeomorph
-- name    : Ehrhart.JetEnvelopeGlobalPlurisubharmonic.jointLogTime_sourceJointPhaseHomeomorph
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:50.716001+00:00
-- url     : https://prove2.me/theorems/f620c610-e072-4f16-9aa1-1ac0ea94dccd
-- title:
--   Ehrhart.JetEnvelopeGlobalPlurisubharmonic.jointLogTime_sourceJointPhaseHomeomorph
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
open Ehrhart.JetEnvelopeGlobalPlurisubharmonic
open Set Filter MeasureTheory Metric
open ActualJetUpperEnvelope JetEnvelopeRightDerivative
open scoped BigOperators Topology ENNReal InnerProductSpace

theorem Ehrhart.JetEnvelopeGlobalPlurisubharmonic.jointLogTime_sourceJointPhaseHomeomorph {n : ℕ}
    (u : ℂ) (hu : ‖u‖ = 1)
    (q : PositiveJointLogSpace n) :
    jointLogTime (sourceJointPhaseHomeomorph u hu q) =
      jointLogTime q := by sorry
