-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetTorusEnvelope_momentTorusEnvelopeTimeSlice_le_normalized_add
-- name    : Ehrhart.BergmanJetTorusEnvelope.momentTorusEnvelopeTimeSlice_le_normalized_add
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:50.716001+00:00
-- url     : https://prove2.me/theorems/78350795-1b70-4bd5-ae9d-13e57294564f
-- title:
--   Ehrhart.BergmanJetTorusEnvelope.momentTorusEnvelopeTimeSlice_le_normalized_add
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

theorem Ehrhart.BergmanJetTorusEnvelope.momentTorusEnvelopeTimeSlice_le_normalized_add
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (q : LogTorus n) {t : ℝ} (ht : 0 < t) :
    momentTorusEnvelopeTimeSlice K F htransport p q t ≤
      momentNormalizedPotential F q.1 +
        BodyScale.canonicalScale K * t := by sorry
