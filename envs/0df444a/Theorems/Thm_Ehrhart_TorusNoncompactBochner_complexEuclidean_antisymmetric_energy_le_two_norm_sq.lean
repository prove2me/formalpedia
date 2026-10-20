-- Prove2me | Theorems.Thm_Ehrhart_TorusNoncompactBochner_complexEuclidean_antisymmetric_energy_le_two_norm_sq
-- name    : Ehrhart.TorusNoncompactBochner.complexEuclidean_antisymmetric_energy_le_two_norm_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:55:01.857667+00:00
-- url     : https://prove2.me/theorems/9c8a4ebb-da17-48a2-b7b9-7c14b45d4a09
-- title:
--   Ehrhart.TorusNoncompactBochner.complexEuclidean_antisymmetric_energy_le_two_norm_sq
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
open Ehrhart.TorusNoncompactBochner
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert TorusCharacters ComplexKillingSaturationBridge MatrixTorusBochnerIdentity
open MatrixTorusBochnerCore MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault WeightedTorusBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff

theorem Ehrhart.TorusNoncompactBochner.complexEuclidean_antisymmetric_energy_le_two_norm_sq
    {n : ℕ}
    (M : EuclideanSpace ℂ (Fin n × Fin n)) :
    ((∑ i : Fin n, ∑ j : Fin n,
      (M (i, j) - M (j, i)) *
        conj (M (i, j) - M (j, i))) / 2 : ℂ).re
      ≤ 2 * ‖M‖ ^ 2 := by sorry
