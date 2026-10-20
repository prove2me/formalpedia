-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetUpperTaggedMonomialObservableConvergence_ae_tendsto_momentTaggedLaurentObservable_interior_unitPartition_tag
-- name    : Ehrhart.BergmanJetUpperTaggedMonomialObservableConvergence.ae_tendsto_momentTaggedLaurentObservable_interior_unitPartition_tag
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:15.527216+00:00
-- url     : https://prove2.me/theorems/6b2be251-1509-4cb5-9531-4a0c0fa57b75
-- title:
--   Ehrhart.BergmanJetUpperTaggedMonomialObservableConvergence.ae_tendsto_momentTaggedLaurentObservable_interior_unitPartition_tag
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

theorem Ehrhart.BergmanJetUpperTaggedMonomialObservableConvergence.ae_tendsto_momentTaggedLaurentObservable_interior_unitPartition_tag
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (f : Space n → ℝ)
    (hf : Continuous f)
    (C : ℝ)
    (hC : ∀ x : Space n, |f x| ≤ C) :
    ∀ᵐ x : Space n
      ∂(volume : Measure (Space n)),
      Tendsto
        (fun k : ℕ =>
          (interior K.carrier).indicator
            (momentTaggedLaurentObservable F (k + 1) f)
            (BoxIntegral.unitPartition.tag (k + 1)
              (BoxIntegral.unitPartition.index (k + 1) x)))
        atTop
        (𝓝 ((interior K.carrier).indicator
          (fun u : Space n =>
            f (SpatialBergmanFatouScheffe.actualGradient
              (legendreTransform F.potential) u)) x)) := by sorry
