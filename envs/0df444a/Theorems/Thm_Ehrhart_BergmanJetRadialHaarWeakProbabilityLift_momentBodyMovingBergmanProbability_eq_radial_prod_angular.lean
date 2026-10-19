-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetRadialHaarWeakProbabilityLift_momentBodyMovingBergmanProbability_eq_radial_prod_angular
-- name    : Ehrhart.BergmanJetRadialHaarWeakProbabilityLift.momentBodyMovingBergmanProbability_eq_radial_prod_angular
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:14.348624+00:00
-- url     : https://prove2.me/theorems/717df904-6a87-45d3-acf1-7f47d12f460c
-- title:
--   Ehrhart.BergmanJetRadialHaarWeakProbabilityLift.momentBodyMovingBergmanProbability_eq_radial_prod_angular
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
open Ehrhart.BergmanJetRadialHaarWeakProbabilityLift
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert BergmanNormalization LogPartitionConvexity MomentOptimizer
open MomentWeakFirstVariation MomentFirstVariation MomentTargetGeodesic MomentRegularity
open MomentWeakBergman MomentWeakBergmanProbabilityEndpoint BergmanJetPartitionEndpoint
open BergmanJetTorusSlopeBridge BergmanJetBergmanProbabilityTransfer
open BergmanJetPortmanteauActualVolumeBridge
open scoped BigOperators ENNReal NNReal Topology BoundedContinuousFunction

theorem Ehrhart.BergmanJetRadialHaarWeakProbabilityLift.momentBodyMovingBergmanProbability_eq_radial_prod_angular
    {n : ℕ} (K : CenteredBody n) (k : ℕ) :
    momentBodyMovingBergmanProbability K k =
      (momentMovingRadialBergmanProbability
        K (momentBodyOptimizer K)
          (momentBodyOptimizer_transport K) k).prod
            (momentNormalizedAngularHaarProbability n) := by sorry
