-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetUpperTaggedMonomialObservableConvergence_tendsto_momentTaggedLaurentObservable_unitPartition_tag
-- name    : Ehrhart.BergmanJetUpperTaggedMonomialObservableConvergence.tendsto_momentTaggedLaurentObservable_unitPartition_tag
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:15.527216+00:00
-- url     : https://prove2.me/theorems/29ba8829-f60c-4ded-93a1-bd098f50d283
-- title:
--   Ehrhart.BergmanJetUpperTaggedMonomialObservableConvergence.tendsto_momentTaggedLaurentObservable_unitPartition_tag
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
open Ehrhart.BergmanJetUpperTaggedMonomialObservableConvergence
open Set Function Filter MeasureTheory
open LaplaceAsymptotics LatticeAsymptotics MomentOptimizer MomentFirstVariation MomentTargetGeodesic
open BergmanJetDualGradientConcentration BergmanJetMovingMonomialObservableConvergence
open BergmanJetRoundedMonomialObservableConvergence BergmanJetTriangularLatticeConvergence
open BergmanJetDiagonalObservableLatticeIdentity
open scoped BigOperators ENNReal NNReal Topology

theorem Ehrhart.BergmanJetUpperTaggedMonomialObservableConvergence.tendsto_momentTaggedLaurentObservable_unitPartition_tag
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier)
    (hdu : DifferentiableAt ℝ (legendreTransform F.potential) u)
    (f : Space n → ℝ)
    (hf : Continuous f)
    (C : ℝ)
    (hC : ∀ x : Space n, |f x| ≤ C) :
    Tendsto
      (fun k : ℕ =>
        momentTaggedLaurentObservable F (k + 1) f
          (BoxIntegral.unitPartition.tag (k + 1)
            (BoxIntegral.unitPartition.index (k + 1) u)))
      atTop
      (𝓝 (f
        (SpatialBergmanFatouScheffe.actualGradient
          (legendreTransform F.potential) u))) := by sorry
