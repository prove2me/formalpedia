-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetTorusEnvelope_momentEnvelopeTimeSlice_le_normalized_add
-- name    : Ehrhart.BergmanJetTorusEnvelope.momentEnvelopeTimeSlice_le_normalized_add
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:50.716001+00:00
-- url     : https://prove2.me/theorems/9d54d8e9-3b4e-4dbc-af1c-9f117482eb9a
-- title:
--   Ehrhart.BergmanJetTorusEnvelope.momentEnvelopeTimeSlice_le_normalized_add
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
open Ehrhart.BergmanJetTorusEnvelope
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert BergmanDiagonalBasisIndependence MomentOptimizer
open MomentFirstVariation MomentTargetGeodesic MomentRegularity MomentWeakBergman
open BergmanJetUpperEnvelope BergmanJetEnvelopeLimit JetEnvelopeRightDerivative
open scoped BigOperators ENNReal Topology

theorem Ehrhart.BergmanJetTorusEnvelope.momentEnvelopeTimeSlice_le_normalized_add
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : LogSpace n) {t : ℝ} (ht : 0 < t) :
    momentEnvelopeTimeSlice K F htransport p z t ≤
      momentNormalizedPotential F (realLogCoordinate z) +
        BodyScale.canonicalScale K * t := by sorry
