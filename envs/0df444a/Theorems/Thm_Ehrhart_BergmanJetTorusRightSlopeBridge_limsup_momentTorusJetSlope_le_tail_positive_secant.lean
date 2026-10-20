-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeBridge_limsup_momentTorusJetSlope_le_tail_positive_secant
-- name    : Ehrhart.BergmanJetTorusRightSlopeBridge.limsup_momentTorusJetSlope_le_tail_positive_secant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:06.698159+00:00
-- url     : https://prove2.me/theorems/78ce6a88-8b19-46a3-afbd-a49fbe71e49b
-- title:
--   Ehrhart.BergmanJetTorusRightSlopeBridge.limsup_momentTorusJetSlope_le_tail_positive_secant
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
open Ehrhart.BergmanJetTorusRightSlopeBridge
open Set Function Filter MeasureTheory Metric
open TorusCharacters WeightedTorusHilbert SupportFunction LaplaceAsymptotics BergmanMonomials
open BergmanGeodesicConvexity JetEnvelopeRightDerivative ActualJetUpperEnvelope MomentOptimizer
open MomentTargetGeodesic MomentFirstVariation MomentRegularity MomentWeakGlobalKernel
open BergmanJetGeodesic BergmanJetProfileBridge BergmanJetRealGeodesic BergmanJetUpperEnvelope
open BergmanJetEnvelopeLimit BergmanJetTorusEnvelope BergmanJetTorusSlopeBridge
open BergmanJetPointwiseLogKernel
open scoped BigOperators ENNReal InnerProductSpace Topology

theorem Ehrhart.BergmanJetTorusRightSlopeBridge.limsup_momentTorusJetSlope_le_tail_positive_secant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (q : LogTorus n)
    {u : Space n} (hu : u ∈ interior K.carrier)
    (hmax : ∀ x : Space n,
      phase u (momentNormalizedPotential F) x ≤
        phase u (momentNormalizedPotential F) q.1)
    (r : ℕ) {t : ℝ} (ht : 0 < t) :
    Filter.limsup
        (fun k : ℕ =>
          momentTorusJetSlope K F htransport p k q) atTop ≤
      (momentJointTailUpperEnvelope K F htransport p r
          (sourcePositiveJointTimePoint
            (sourceTorusCoverPoint q) t ht) -
        momentNormalizedPotential F q.1) / t := by sorry
