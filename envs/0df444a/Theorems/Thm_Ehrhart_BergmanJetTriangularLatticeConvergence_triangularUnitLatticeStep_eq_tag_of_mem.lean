-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetTriangularLatticeConvergence_triangularUnitLatticeStep_eq_tag_of_mem
-- name    : Ehrhart.BergmanJetTriangularLatticeConvergence.triangularUnitLatticeStep_eq_tag_of_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:14.348624+00:00
-- url     : https://prove2.me/theorems/753b917a-1692-4430-a7b4-3ead2d319475
-- title:
--   Ehrhart.BergmanJetTriangularLatticeConvergence.triangularUnitLatticeStep_eq_tag_of_mem
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
open Ehrhart.BergmanJetTriangularLatticeConvergence
open Set Filter MeasureTheory Metric
open LatticeAsymptotics
open scoped BigOperators ENNReal NNReal Topology

theorem Ehrhart.BergmanJetTriangularLatticeConvergence.triangularUnitLatticeStep_eq_tag_of_mem {n : ℕ}
    (B : BoxIntegral.Box (Fin n))
    (hB : BoxIntegral.hasIntegralVertices B)
    (s : Set (Space n))
    (G : ℕ → Space n → ℝ)
    (k : ℕ) (x : Space n)
    (hx : x ∈ (B : Set (Space n))) :
    triangularUnitLatticeStep B s G k x =
      s.indicator (G (k + 1))
        (BoxIntegral.unitPartition.tag (k + 1)
          (BoxIntegral.unitPartition.index (k + 1) x)) := by sorry
