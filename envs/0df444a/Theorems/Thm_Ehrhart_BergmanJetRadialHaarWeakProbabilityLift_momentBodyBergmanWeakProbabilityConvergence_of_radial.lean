-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetRadialHaarWeakProbabilityLift_momentBodyBergmanWeakProbabilityConvergence_of_radial
-- name    : Ehrhart.BergmanJetRadialHaarWeakProbabilityLift.momentBodyBergmanWeakProbabilityConvergence_of_radial
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:14.348624+00:00
-- url     : https://prove2.me/theorems/2371c878-f6be-430a-bfdc-c498064b25e2
-- title:
--   Ehrhart.BergmanJetRadialHaarWeakProbabilityLift.momentBodyBergmanWeakProbabilityConvergence_of_radial
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

theorem Ehrhart.BergmanJetRadialHaarWeakProbabilityLift.momentBodyBergmanWeakProbabilityConvergence_of_radial
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n)
    (hrad : Tendsto
      (momentMovingRadialBergmanProbability
        K (momentBodyOptimizer K)
          (momentBodyOptimizer_transport K))
      atTop
      (𝓝 (momentRadialGibbsProbability
        (momentBodyOptimizer K)))) :
    Tendsto (momentBodyMovingBergmanProbability K) atTop
      (𝓝 (momentBodyZeroGibbsProbability K p)) := by sorry
