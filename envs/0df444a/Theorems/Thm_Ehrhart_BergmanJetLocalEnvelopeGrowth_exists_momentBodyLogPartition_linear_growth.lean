-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetLocalEnvelopeGrowth_exists_momentBodyLogPartition_linear_growth
-- name    : Ehrhart.BergmanJetLocalEnvelopeGrowth.exists_momentBodyLogPartition_linear_growth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:12.329469+00:00
-- url     : https://prove2.me/theorems/02fd3bca-1387-43bc-99fb-149020cea016
-- title:
--   Ehrhart.BergmanJetLocalEnvelopeGrowth.exists_momentBodyLogPartition_linear_growth
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

theorem Ehrhart.BergmanJetLocalEnvelopeGrowth.exists_momentBodyLogPartition_linear_growth
    {n : ℕ} (K : CenteredBody n) :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
      momentBodyLogPartition K (0 : LogSpace n) t ≤
        (n : ℝ) * t + C := by sorry
