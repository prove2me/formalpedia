-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetSpatialPeriodicity_momentJointTailUpperEnvelope_spatial_invariant
-- name    : Ehrhart.BergmanJetSpatialPeriodicity.momentJointTailUpperEnvelope_spatial_invariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:50.716001+00:00
-- url     : https://prove2.me/theorems/26937c5e-807d-4d7e-8d7a-8d47c682f4a7
-- title:
--   Ehrhart.BergmanJetSpatialPeriodicity.momentJointTailUpperEnvelope_spatial_invariant
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
open Ehrhart.BergmanJetSpatialPeriodicity
open Set Function Filter MeasureTheory
open TorusCharacters AdaptedBergmanBasis BergmanMonomials MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic BergmanJetBasis BergmanJetGeodesic BergmanJetRealGeodesic
open BergmanJetUpperEnvelope ActualJetUpperEnvelope JetEnvelopeGlobalPlurisubharmonic
open EnvelopeSpatialPeriodicity
open scoped BigOperators Topology

theorem Ehrhart.BergmanJetSpatialPeriodicity.momentJointTailUpperEnvelope_spatial_invariant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ) (m : Fin n → ℤ)
    (q : PositiveJointLogSpace n) :
    momentJointTailUpperEnvelope K F htransport p r
        (sourceJointSpatialDeckHomeomorph m q) =
      momentJointTailUpperEnvelope K F htransport p r q := by sorry
