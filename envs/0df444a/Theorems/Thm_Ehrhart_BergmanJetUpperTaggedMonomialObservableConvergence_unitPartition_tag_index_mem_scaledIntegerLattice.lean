-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetUpperTaggedMonomialObservableConvergence_unitPartition_tag_index_mem_scaledIntegerLattice
-- name    : Ehrhart.BergmanJetUpperTaggedMonomialObservableConvergence.unitPartition_tag_index_mem_scaledIntegerLattice
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:15.527216+00:00
-- url     : https://prove2.me/theorems/7d9541f8-7af7-4a0c-82ed-b008d5f69590
-- title:
--   Ehrhart.BergmanJetUpperTaggedMonomialObservableConvergence.unitPartition_tag_index_mem_scaledIntegerLattice
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

theorem Ehrhart.BergmanJetUpperTaggedMonomialObservableConvergence.unitPartition_tag_index_mem_scaledIntegerLattice
    {n : ℕ} (k : ℕ) (u : Space n) :
    BoxIntegral.unitPartition.tag (k + 1)
        (BoxIntegral.unitPartition.index (k + 1) u) ∈
      scaledIntegerLattice n (k + 1) := by sorry
