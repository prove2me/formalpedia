-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetEnvelopeLimit_momentJointUpperEnvelope_le_majorant
-- name    : Ehrhart.BergmanJetEnvelopeLimit.momentJointUpperEnvelope_le_majorant
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:48.222718+00:00
-- url     : https://prove2.me/theorems/bed930fa-3648-4850-8831-fa867110a95e
-- title:
--   Ehrhart.BergmanJetEnvelopeLimit.momentJointUpperEnvelope_le_majorant
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
open Ehrhart.BergmanJetEnvelopeLimit
open Set Function Filter MeasureTheory Module
open MomentOptimizer MomentFirstVariation MomentTargetGeodesic BergmanJetUpperEnvelope
open BergmanJetEnvelopePlurisubharmonic ActualJetUpperEnvelope
open scoped BigOperators ENNReal InnerProductSpace Topology

theorem Ehrhart.BergmanJetEnvelopeLimit.momentJointUpperEnvelope_le_majorant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (q : PositiveJointLogSpace n) :
    momentJointUpperEnvelope K F htransport p q ≤
      momentJointMajorant K F q := by sorry
