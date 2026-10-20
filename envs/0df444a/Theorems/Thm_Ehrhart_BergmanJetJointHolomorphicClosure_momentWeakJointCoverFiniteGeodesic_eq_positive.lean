-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicClosure_momentWeakJointCoverFiniteGeodesic_eq_positive
-- name    : Ehrhart.BergmanJetJointHolomorphicClosure.momentWeakJointCoverFiniteGeodesic_eq_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:00.136627+00:00
-- url     : https://prove2.me/theorems/9d128131-1af0-4a47-82e7-0c64d4b53a5f
-- title:
--   Ehrhart.BergmanJetJointHolomorphicClosure.momentWeakJointCoverFiniteGeodesic_eq_positive
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
open Ehrhart.BergmanJetJointHolomorphicClosure
open Set Function Filter MeasureTheory Metric
open TorusCharacters BergmanMonomials BergmanDiagonalBasisIndependence MomentOptimizer
open MomentTargetGeodesic MomentFirstVariation MomentRegularity MomentWeakBergman BergmanJetGeodesic
open BergmanJetRealGeodesic BergmanJetUpperEnvelope BergmanJetEnvelopePlurisubharmonic
open BergmanJetEnvelopeLimit BergmanJetJointEnvelopeRegularization BergmanJetJointHolomorphicPhase
open ActualJetUpperEnvelope ActualJetPlurisubharmonicEnvelope JetEnvelopeRightDerivative
open JetEnvelopeGlobalPlurisubharmonic JetEnvelopeGlobalPlurisubharmonicClosure
open BergmanGeodesicConvexity
open scoped BigOperators ENNReal Topology InnerProductSpace

theorem Ehrhart.BergmanJetJointHolomorphicClosure.momentWeakJointCoverFiniteGeodesic_eq_positive
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ)
    (q : SourceJointComplexCover n)
    (hq : 0 < sourceJointCoverTime q) :
    momentWeakJointCoverFiniteGeodesic K F htransport p k q =
      momentPositiveJointGeodesic K F htransport p k
        (sourceJointExpPositiveLift q hq) := by sorry
