-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetUpperEnvelope_momentJointTailSup_antitone
-- name    : Ehrhart.BergmanJetUpperEnvelope.momentJointTailSup_antitone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:48.222718+00:00
-- url     : https://prove2.me/theorems/0c0e60cb-e82a-4935-96d8-6e814ab62d8e
-- title:
--   Ehrhart.BergmanJetUpperEnvelope.momentJointTailSup_antitone
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
open Ehrhart.BergmanJetUpperEnvelope
open Set Function Filter MeasureTheory Module
open MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity MomentWeakBergman
open BergmanJetGeodesic BergmanJetRealGeodesic ActualJetUpperEnvelope
open scoped BigOperators ENNReal InnerProductSpace Topology

theorem Ehrhart.BergmanJetUpperEnvelope.momentJointTailSup_antitone
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    {r s : ℕ} (hrs : r ≤ s)
    (q : PositiveJointLogSpace n) :
    momentJointTailSup K F htransport p s q ≤
      momentJointTailSup K F htransport p r q := by sorry
