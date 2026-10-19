-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicPhase_momentWeakJointCoverEnvelope_eq_holomorphicExpLift_of_pos
-- name    : Ehrhart.BergmanJetJointHolomorphicPhase.momentWeakJointCoverEnvelope_eq_holomorphicExpLift_of_pos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:00.136627+00:00
-- url     : https://prove2.me/theorems/1baafd1a-561e-43eb-a399-1b35ebd1f611
-- title:
--   Ehrhart.BergmanJetJointHolomorphicPhase.momentWeakJointCoverEnvelope_eq_holomorphicExpLift_of_pos
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
open Ehrhart.BergmanJetJointHolomorphicPhase
open Set Function Filter MeasureTheory
open TorusCharacters MomentOptimizer MomentTargetGeodesic MomentFirstVariation
open BergmanJetUpperEnvelope BergmanJetEnvelopeLimit BergmanJetJointEnvelopeRegularization
open ActualJetUpperEnvelope JetEnvelopeRightDerivative JetEnvelopeGlobalPlurisubharmonic
open scoped BigOperators ENNReal Topology

theorem Ehrhart.BergmanJetJointHolomorphicPhase.momentWeakJointCoverEnvelope_eq_holomorphicExpLift_of_pos
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (q : SourceJointComplexCover n)
    (hq : 0 < sourceJointCoverTime q) :
    momentWeakJointCoverEnvelope K F htransport p q =
      momentJointUpperEnvelope K F htransport p
        (sourceJointExpPositiveLift q hq) := by sorry
