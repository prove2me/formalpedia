-- Prove2me | Theorems.Thm_Ehrhart_SimplexVolume_centered_integral_zero_of_coordinate_tails
-- name    : Ehrhart.SimplexVolume.centered_integral_zero_of_coordinate_tails
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:46.631058+00:00
-- url     : https://prove2.me/theorems/e55d8277-1a49-4fbb-bb93-444fd3f3f7b7
-- title:
--   Ehrhart.SimplexVolume.centered_integral_zero_of_coordinate_tails
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
open Ehrhart.SimplexVolume
open Set MeasureTheory
open scoped BigOperators ENNReal Pointwise

theorem Ehrhart.SimplexVolume.centered_integral_zero_of_coordinate_tails
    {n : ℕ} (K : Set (Space n)) (hK : IsCompact K) (v : ℝ)
    (hT : ∀ y, y ∈ K ↔
      (∀ j, -(1 : ℝ) ≤ y j) ∧ (∑ j, y j) ≤ 1)
    (htail : ∀ (i : Fin n) {t : ℝ}, 0 ≤ t → t < (n : ℝ) + 1 →
      ((volume : Measure (Space n)).restrict K).real
        {y | t ≤ y i + 1} = (((n : ℝ) + 1) - t) ^ n * v) :
    (∫ y in K, y) = (0 : Space n) := by sorry
