-- Prove2me | Theorems.Thm_Ehrhart_SimplexVolume_centeredSimplex_coordinate_tail_measure
-- name    : Ehrhart.SimplexVolume.centeredSimplex_coordinate_tail_measure
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:46.631058+00:00
-- url     : https://prove2.me/theorems/d0008505-d3c8-4d37-89cc-725fed382d91
-- title:
--   Ehrhart.SimplexVolume.centeredSimplex_coordinate_tail_measure
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

theorem Ehrhart.SimplexVolume.centeredSimplex_coordinate_tail_measure {n : ℕ}
    (T : Set (Space n))
    (hT : ∀ y, y ∈ T ↔
      (∀ j, -(1 : ℝ) ≤ y j) ∧ (∑ j, y j) ≤ 1)
    (i : Fin n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < (n : ℝ) + 1) :
    ((volume : Measure (Space n)).restrict T).real
        {y : Space n | t ≤ y i + 1} =
      ((n : ℝ) + 1 - t) ^ n *
        (volume : Measure (Space n)).real
          (standardSimplex n) := by sorry
