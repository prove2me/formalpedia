-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetUpperEnvelope_momentJointTailUpperEnvelope_le_majorant_add_one
-- name    : Ehrhart.BergmanJetUpperEnvelope.momentJointTailUpperEnvelope_le_majorant_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:48.222718+00:00
-- url     : https://prove2.me/theorems/fec42f67-5b14-44b3-aaae-bcc931b1d917
-- title:
--   Ehrhart.BergmanJetUpperEnvelope.momentJointTailUpperEnvelope_le_majorant_add_one
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

theorem Ehrhart.BergmanJetUpperEnvelope.momentJointTailUpperEnvelope_le_majorant_add_one
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (r : ℕ) (q : PositiveJointLogSpace n) :
    momentJointTailUpperEnvelope K F htransport p r q ≤
      momentJointMajorant K F q + 1 := by sorry
