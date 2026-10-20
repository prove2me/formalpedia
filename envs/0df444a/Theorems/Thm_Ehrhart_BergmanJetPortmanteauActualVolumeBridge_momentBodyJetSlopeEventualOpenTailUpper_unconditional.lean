-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetPortmanteauActualVolumeBridge_momentBodyJetSlopeEventualOpenTailUpper_unconditional
-- name    : Ehrhart.BergmanJetPortmanteauActualVolumeBridge.momentBodyJetSlopeEventualOpenTailUpper_unconditional
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:12.329469+00:00
-- url     : https://prove2.me/theorems/06398ac5-be09-4af8-9ab9-c4d66665b508
-- title:
--   Ehrhart.BergmanJetPortmanteauActualVolumeBridge.momentBodyJetSlopeEventualOpenTailUpper_unconditional
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
open Ehrhart.BergmanJetPortmanteauActualVolumeBridge
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert JetEnvelopeRightDerivative LogPartitionConvexity
open MomentRegularity BergmanJetUpperEnvelope BergmanJetEnvelopeLimit BergmanJetTorusEnvelope
open BergmanJetPartitionEndpoint BergmanJetTorusSlopeBridge BergmanJetTorusRightSlopeBridge
open BergmanJetTorusRightSlopeGibbsBridge BergmanJetBodyExponentialSecantBridge
open BergmanJetPortmanteauMovingUpperTailBridge BergmanJetPortmanteauActualUpperTailBridge
open BergmanJetTorusSlopeJointNeighborhoodUpper
open scoped BigOperators ENNReal NNReal Topology

theorem Ehrhart.BergmanJetPortmanteauActualVolumeBridge.momentBodyJetSlopeEventualOpenTailUpper_unconditional
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (r : ℕ) (t : ℝ) (ht : 0 < t) :
    ∀ (q : LogTorus n) (a : ℝ),
      momentBodyClampedTailPositiveSecant K p r t ht q < a →
        ∃ (N : ℕ) (U : Set (LogTorus n)), IsOpen U ∧ q ∈ U ∧
          ∀ k : ℕ, N ≤ k → ∀ y ∈ U,
            momentTorusJetSlope
              K (momentBodyOptimizer K)
                (momentBodyOptimizer_transport K) p (k + 1) y < a := by sorry
