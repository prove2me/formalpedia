-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetRadialHaarWeakProbabilityLift_momentBodyZeroGibbsProbability_eq_radial_prod_angular
-- name    : Ehrhart.BergmanJetRadialHaarWeakProbabilityLift.momentBodyZeroGibbsProbability_eq_radial_prod_angular
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:14.348624+00:00
-- url     : https://prove2.me/theorems/d4693c1d-c13f-4507-8952-5d29793b1b5e
-- title:
--   Ehrhart.BergmanJetRadialHaarWeakProbabilityLift.momentBodyZeroGibbsProbability_eq_radial_prod_angular
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

theorem Ehrhart.BergmanJetRadialHaarWeakProbabilityLift.momentBodyZeroGibbsProbability_eq_radial_prod_angular
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) :
    momentBodyZeroGibbsProbability K p =
      (momentRadialGibbsProbability
        (momentBodyOptimizer K)).prod
          (momentNormalizedAngularHaarProbability n) := by sorry
