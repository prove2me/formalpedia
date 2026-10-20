-- Prove2me | Theorems.Thm_Ehrhart_Volume_momentBodyBergmanWeakProbabilityConvergence_unconditional
-- name    : Ehrhart.Volume.momentBodyBergmanWeakProbabilityConvergence_unconditional
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:15.527216+00:00
-- url     : https://prove2.me/theorems/4ce12671-3504-4b20-918e-868c7939e770
-- title:
--   Ehrhart.Volume.momentBodyBergmanWeakProbabilityConvergence_unconditional
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
open Ehrhart.Volume
open Set Function Filter MeasureTheory
open TorusCharacters LatticeAsymptotics BergmanMonomials BergmanNormalization LaplaceAsymptotics
open MomentOptimizer MomentWeakFirstVariation MomentFirstVariation MomentTargetGeodesic
open MomentRegularity BergmanJetPartitionEndpoint BergmanJetTriangularLatticeConvergence
open BergmanJetDiagonalObservableLatticeIdentity BergmanJetDualGradientInverseTransport
open BergmanJetUpperTaggedMonomialObservableConvergence BergmanJetPortmanteauActualVolumeBridge
open BergmanJetRadialHaarWeakProbabilityLift
open scoped BigOperators ENNReal NNReal Topology BoundedContinuousFunction

theorem Ehrhart.Volume.momentBodyBergmanWeakProbabilityConvergence_unconditional
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) :
    Tendsto (momentBodyMovingBergmanProbability K) atTop
      (𝓝 (momentBodyZeroGibbsProbability K p)) := by sorry
