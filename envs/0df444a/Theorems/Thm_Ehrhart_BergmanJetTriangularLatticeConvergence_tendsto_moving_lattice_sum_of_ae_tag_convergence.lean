-- Prove2me | Theorems.Thm_Ehrhart_BergmanJetTriangularLatticeConvergence_tendsto_moving_lattice_sum_of_ae_tag_convergence
-- name    : Ehrhart.BergmanJetTriangularLatticeConvergence.tendsto_moving_lattice_sum_of_ae_tag_convergence
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:14.348624+00:00
-- url     : https://prove2.me/theorems/975d3388-7006-45d9-b637-dd8e1f7753de
-- title:
--   Ehrhart.BergmanJetTriangularLatticeConvergence.tendsto_moving_lattice_sum_of_ae_tag_convergence
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

theorem Ehrhart.BergmanJetTriangularLatticeConvergence.tendsto_moving_lattice_sum_of_ae_tag_convergence {n : ℕ}
    (B : BoxIntegral.Box (Fin n))
    (hB : BoxIntegral.hasIntegralVertices B)
    (s : Set (Space n))
    (hs : s ⊆ (B : Set (Space n)))
    (hsm : MeasurableSet s)
    (G : ℕ → Space n → ℝ)
    (g : Space n → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ k : ℕ, 0 < k → ∀ u ∈ s,
      u ∈ scaledIntegerLattice n k → ‖G k u‖ ≤ C)
    (hpoint : ∀ᵐ x : Space n
        ∂(volume : Measure (Space n)),
      Tendsto (fun k : ℕ =>
        s.indicator (G (k + 1))
          (BoxIntegral.unitPartition.tag (k + 1)
            (BoxIntegral.unitPartition.index (k + 1) x)))
        atTop (𝓝 (s.indicator g x))) :
    Tendsto
      (fun k : ℕ =>
        (∑' u : ↑(s ∩ scaledIntegerLattice n (k + 1)),
          G (k + 1) u) / ((k + 1 : ℕ) : ℝ) ^ n)
      atTop (𝓝 (∫ x in s, g x
        ∂(volume : Measure (Space n)))) := by sorry
