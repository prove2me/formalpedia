-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetJointHolomorphicConvexTransfer_convexOn_momentBodyLogPartition_Ici_of_holomorphicStrict
-- name    : Ehrhart.BergmanJetJointHolomorphicConvexTransfer.convexOn_momentBodyLogPartition_Ici_of_holomorphicStrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:09.94113+00:00
-- url     : https://prove2.me/theorems/7518beb1-1c86-4db2-ab57-c9babe70325a
-- title:
--   Ehrhart.BergmanJetJointHolomorphicConvexTransfer.convexOn_momentBodyLogPartition_Ici_of_holomorphicStrict
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
open Ehrhart.BergmanJetJointHolomorphicConvexTransfer
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert MomentOptimizer MomentTargetGeodesic MomentFirstVariation
open MomentRegularity BergmanJetTorusEnvelope BergmanJetPartitionEndpoint
open BergmanJetJointHolomorphicStrictSchur BergmanJetJointHolomorphicPhysicalApproximation
open JetEnvelopeSlopeConvergence LogPartitionConvexity
open scoped BigOperators ENNReal Topology

theorem Ehrhart.BergmanJetJointHolomorphicConvexTransfer.convexOn_momentBodyLogPartition_Ici_of_holomorphicStrict
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 (0 : ℝ)))
    (hε₀ : ∀ k : ℕ, 0 ≤ ε k)
    (hε₁ : ∀ k : ℕ, ε k ≤ 1)
    (hstrict : ∀ k : ℕ,
      ConvexOn ℝ (Set.Ioi 0)
        (sourceLogPartition
          (momentWeakHolomorphicStrictJointTorusWeight
            K (momentBodyOptimizer K)
              (momentBodyOptimizer_transport K)
              p (ε k) k))) :
    ConvexOn ℝ (Set.Ici 0)
      (momentBodyLogPartition K p) := by sorry
