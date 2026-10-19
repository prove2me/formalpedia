-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetBodyExponentialSecantBridge_integral_momentBodyEnvelopeRelativeDensity_eq_normalizedPartition
-- name    : Ehrhart.BergmanJetBodyExponentialSecantBridge.integral_momentBodyEnvelopeRelativeDensity_eq_normalizedPartition
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:12.329469+00:00
-- url     : https://prove2.me/theorems/a8a34033-1061-48ce-b1cf-611ca3d8cab6
-- title:
--   Ehrhart.BergmanJetBodyExponentialSecantBridge.integral_momentBodyEnvelopeRelativeDensity_eq_normalizedPartition
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
open Ehrhart.BergmanJetBodyExponentialSecantBridge
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence LogPartitionConvexity
open BergmanJetPartitionEndpoint BergmanJetTorusRightSlopeGibbsBridge
open BergmanJetBodyLogPartitionSharpGrowth
open scoped BigOperators ENNReal Topology

theorem Ehrhart.BergmanJetBodyExponentialSecantBridge.integral_momentBodyEnvelopeRelativeDensity_eq_normalizedPartition
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) :
    (∫ q : LogTorus n,
      momentBodyEnvelopeRelativeDensity K p t q
        ∂(sourceProbability (momentBodyTorusWeight K p) 0)) =
      momentBodyNormalizedPartition K p t := by sorry
