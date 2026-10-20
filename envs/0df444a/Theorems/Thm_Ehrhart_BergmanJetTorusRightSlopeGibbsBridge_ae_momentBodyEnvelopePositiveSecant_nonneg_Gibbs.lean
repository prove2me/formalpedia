-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeGibbsBridge_ae_momentBodyEnvelopePositiveSecant_nonneg_Gibbs
-- name    : Ehrhart.BergmanJetTorusRightSlopeGibbsBridge.ae_momentBodyEnvelopePositiveSecant_nonneg_Gibbs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:06.698159+00:00
-- url     : https://prove2.me/theorems/1bd3fe9d-46b4-462b-8dad-94c112654e70
-- title:
--   Ehrhart.BergmanJetTorusRightSlopeGibbsBridge.ae_momentBodyEnvelopePositiveSecant_nonneg_Gibbs
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

theorem Ehrhart.BergmanJetTorusRightSlopeGibbsBridge.ae_momentBodyEnvelopePositiveSecant_nonneg_Gibbs
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ q : LogTorus n
      ∂(sourceProbability (momentBodyTorusWeight K p) 0),
      0 ≤ momentBodyEnvelopePositiveSecant K p t q := by sorry
