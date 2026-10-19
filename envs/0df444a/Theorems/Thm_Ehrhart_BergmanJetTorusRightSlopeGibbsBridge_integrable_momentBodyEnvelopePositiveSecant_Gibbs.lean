-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeGibbsBridge_integrable_momentBodyEnvelopePositiveSecant_Gibbs
-- name    : Ehrhart.BergmanJetTorusRightSlopeGibbsBridge.integrable_momentBodyEnvelopePositiveSecant_Gibbs
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:06.698159+00:00
-- url     : https://prove2.me/theorems/b1ef5eee-1acb-4da2-85cd-aa41aabf4ed0
-- title:
--   Ehrhart.BergmanJetTorusRightSlopeGibbsBridge.integrable_momentBodyEnvelopePositiveSecant_Gibbs
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
open Ehrhart.BergmanJetTorusRightSlopeGibbsBridge
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence LogPartitionConvexity
open MomentOptimizer MomentTargetGeodesic MomentFirstVariation MomentRegularity
open BergmanJetTorusEnvelope BergmanJetPartitionEndpoint BergmanJetTorusSlopeBridge
open BergmanJetTorusRightSlopeBridge
open scoped BigOperators ENNReal Topology

theorem Ehrhart.BergmanJetTorusRightSlopeGibbsBridge.integrable_momentBodyEnvelopePositiveSecant_Gibbs
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) {t : ℝ} (ht : 0 < t) :
    Integrable (momentBodyEnvelopePositiveSecant K p t)
      (sourceProbability (momentBodyTorusWeight K p) 0) := by sorry
