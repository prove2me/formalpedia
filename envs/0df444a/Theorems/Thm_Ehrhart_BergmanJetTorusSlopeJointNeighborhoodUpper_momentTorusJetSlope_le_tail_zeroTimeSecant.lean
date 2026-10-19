-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetTorusSlopeJointNeighborhoodUpper_momentTorusJetSlope_le_tail_zeroTimeSecant
-- name    : Ehrhart.BergmanJetTorusSlopeJointNeighborhoodUpper.momentTorusJetSlope_le_tail_zeroTimeSecant
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:12.329469+00:00
-- url     : https://prove2.me/theorems/51c7390e-52d2-4e78-82e4-af122d9204b4
-- title:
--   Ehrhart.BergmanJetTorusSlopeJointNeighborhoodUpper.momentTorusJetSlope_le_tail_zeroTimeSecant
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
open Ehrhart.BergmanJetTorusSlopeJointNeighborhoodUpper
open Set Function Filter MeasureTheory Metric
open TorusCharacters WeightedTorusHilbert BergmanMonomials JetEnvelopeRightDerivative
open MomentOptimizer MomentTargetGeodesic MomentFirstVariation MomentRegularity MomentWeakBergman
open BergmanJetRealGeodesic BergmanJetUpperEnvelope BergmanJetTorusSlopeBridge
open BergmanJetTorusRightSlopeBridge BergmanJetGlobalLogKernelEquiLipschitz
open BergmanJetPortmanteauActualUpperTailBridge
open scoped BigOperators ENNReal NNReal Topology

theorem Ehrhart.BergmanJetTorusSlopeJointNeighborhoodUpper.momentTorusJetSlope_le_tail_zeroTimeSecant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r k : ℕ)
    (hk : momentJointTailStart K F htransport p + r + 1 ≤ k)
    (q : LogTorus n) (t : ℝ) (ht : 0 < t) :
    momentTorusJetSlope K F htransport p k q ≤
      (momentTorusTailUpperEnvelopeTimeSlice
          K F htransport p r t ht q -
        Real.log
          (diagonalKernel K k
            (momentNormalizedPotential F) q.1) /
              (k : ℝ)) / t := by sorry
