-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetLocalEnvelopeGrowth_eventually_momentPositiveJointGeodesic_local_le_maximum_add
-- name    : Ehrhart.BergmanJetLocalEnvelopeGrowth.eventually_momentPositiveJointGeodesic_local_le_maximum_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:12.329469+00:00
-- url     : https://prove2.me/theorems/f6dfb62f-4c59-4310-b1de-c6d6f2827496
-- title:
--   Ehrhart.BergmanJetLocalEnvelopeGrowth.eventually_momentPositiveJointGeodesic_local_le_maximum_add
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
open Ehrhart.BergmanJetLocalEnvelopeGrowth
open Set Function Filter MeasureTheory Module Metric
open TorusCharacters WeightedTorusHilbert MomentOptimizer MomentFirstVariation MomentTargetGeodesic
open BergmanJetUpperEnvelope BergmanJetEnvelopeLimit BergmanJetTorusEnvelope
open BergmanJetPartitionEndpoint BergmanJetLocalGrowth ActualJetUpperEnvelope
open JetEnvelopeSlopeConvergence JetEnvelopeRightDerivative JetEnvelopeLocalGrowth
open LogPartitionConvexity
open scoped BigOperators ENNReal Topology

theorem Ehrhart.BergmanJetLocalEnvelopeGrowth.eventually_momentPositiveJointGeodesic_local_le_maximum_add
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (R : ℝ) (hR : 0 < R)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ w ∈ sourceLocalJointRegion p R,
      momentPositiveJointGeodesic K F htransport p k w ≤
        momentLocalPotentialMaximum K F p R + ε := by sorry
