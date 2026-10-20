-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetTorusSlopeJointNeighborhoodUpper_eventual_open_momentTorusJetSlope_lt_clampedTailSecant
-- name    : Ehrhart.BergmanJetTorusSlopeJointNeighborhoodUpper.eventual_open_momentTorusJetSlope_lt_clampedTailSecant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:12.329469+00:00
-- url     : https://prove2.me/theorems/ce7aacab-4d2b-4535-9001-4973a31f30a9
-- title:
--   Ehrhart.BergmanJetTorusSlopeJointNeighborhoodUpper.eventual_open_momentTorusJetSlope_lt_clampedTailSecant
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

theorem Ehrhart.BergmanJetTorusSlopeJointNeighborhoodUpper.eventual_open_momentTorusJetSlope_lt_clampedTailSecant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ) (t : ℝ) (ht : 0 < t)
    (q : LogTorus n) (a : ℝ)
    (ha : momentTorusClampedTailPositiveSecant
      K F htransport p r t ht q < a) :
    ∃ (N : ℕ) (U : Set (LogTorus n)),
      IsOpen U ∧ q ∈ U ∧
        ∀ (k : ℕ), N ≤ k → ∀ y ∈ U,
          momentTorusJetSlope K F htransport p k y < a := by sorry
