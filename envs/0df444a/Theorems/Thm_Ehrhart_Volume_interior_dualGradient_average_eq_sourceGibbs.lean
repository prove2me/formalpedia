-- Prove2me | Theorems.Thm_Ehrhart_Volume_interior_dualGradient_average_eq_sourceGibbs
-- name    : Ehrhart.Volume.interior_dualGradient_average_eq_sourceGibbs
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:15.527216+00:00
-- url     : https://prove2.me/theorems/094ce72c-8088-46aa-9db8-34059cc7cda7
-- title:
--   Ehrhart.Volume.interior_dualGradient_average_eq_sourceGibbs
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

theorem Ehrhart.Volume.interior_dualGradient_average_eq_sourceGibbs
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (f : Space n → ℝ)
    (hf : Continuous f) :
    (∫ u in interior K.carrier,
      f (SpatialBergmanFatouScheffe.actualGradient
        (legendreTransform F.potential) u)
      ∂(volume : Measure (Space n))) /
        normalizedVolume K.carrier =
      ∫ x : Space n, f x
        ∂(finiteEnergySourceGibbsProbability F) := by sorry
