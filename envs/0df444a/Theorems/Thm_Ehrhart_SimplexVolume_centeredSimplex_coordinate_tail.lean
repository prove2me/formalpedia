-- Prove2me | Theorems.Thm_Ehrhart_SimplexVolume_centeredSimplex_coordinate_tail
-- name    : Ehrhart.SimplexVolume.centeredSimplex_coordinate_tail
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:54:46.631058+00:00
-- url     : https://prove2.me/theorems/bfaf7897-b83a-4516-a889-7504dbd5452e
-- title:
--   Ehrhart.SimplexVolume.centeredSimplex_coordinate_tail
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

theorem Ehrhart.SimplexVolume.centeredSimplex_coordinate_tail {n : ℕ}
    (T : Set (Space n))
    (hT : ∀ y, y ∈ T ↔
      (∀ j, -(1 : ℝ) ≤ y j) ∧ (∑ j, y j) ≤ 1)
    (i : Fin n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < (n : ℝ) + 1) :
    {y : Space n | y ∈ T ∧ t ≤ y i + 1} =
      (fun x : Space n => x + (Pi.single i t - 1)) ''
        (((n : ℝ) + 1 - t) • standardSimplex n) := by sorry
