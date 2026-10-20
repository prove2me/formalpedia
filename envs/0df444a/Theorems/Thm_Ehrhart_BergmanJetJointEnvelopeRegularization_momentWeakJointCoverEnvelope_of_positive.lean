-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetJointEnvelopeRegularization_momentWeakJointCoverEnvelope_of_positive
-- name    : Ehrhart.BergmanJetJointEnvelopeRegularization.momentWeakJointCoverEnvelope_of_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:00.136627+00:00
-- url     : https://prove2.me/theorems/9f73a1b9-d0dc-40c8-9e8a-1e80f39548c4
-- title:
--   Ehrhart.BergmanJetJointEnvelopeRegularization.momentWeakJointCoverEnvelope_of_positive
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
open Ehrhart.BergmanJetJointEnvelopeRegularization
open Set Function Filter MeasureTheory Metric Matrix
open TorusCharacters BergmanDiagonalBasisIndependence MomentOptimizer MomentTargetGeodesic
open MomentFirstVariation BergmanJetEnvelopeLimit BergmanJetTorusEnvelope JetEnvelopeRightDerivative
open JetEnvelopeGlobalPlurisubharmonic
open scoped BigOperators ENNReal Topology ContDiff Convolution ComplexOrder

theorem Ehrhart.BergmanJetJointEnvelopeRegularization.momentWeakJointCoverEnvelope_of_positive
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (q : SourceJointComplexCover n)
    (hq : 0 < sourceJointCoverTime q) :
    momentWeakJointCoverEnvelope K F htransport p q =
      momentJointUpperEnvelope K F htransport p
        (sourcePositiveJointTimePoint q.1
          (sourceJointCoverTime q) hq) := by sorry
