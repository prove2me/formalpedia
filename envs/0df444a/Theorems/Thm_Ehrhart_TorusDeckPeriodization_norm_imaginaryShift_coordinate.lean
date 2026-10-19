-- Prove2me | Theorems.Thm_Ehrhart_TorusDeckPeriodization_norm_imaginaryShift_coordinate
-- name    : Ehrhart.TorusDeckPeriodization.norm_imaginaryShift_coordinate
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:55:01.857667+00:00
-- url     : https://prove2.me/theorems/fcf3632b-8478-48f0-84d5-5fa73a1c5bf1
-- title:
--   Ehrhart.TorusDeckPeriodization.norm_imaginaryShift_coordinate
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
open Ehrhart.TorusDeckPeriodization
open Set Function Filter MeasureTheory Matrix
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution

theorem Ehrhart.TorusDeckPeriodization.norm_imaginaryShift_coordinate
    {n : ℕ} (q : Fin n → ℤ) (i : Fin n) :
    ‖TorusCharacters.imaginaryShift q i‖ =
      |(q i : ℝ)| * (2 * Real.pi) := by sorry
