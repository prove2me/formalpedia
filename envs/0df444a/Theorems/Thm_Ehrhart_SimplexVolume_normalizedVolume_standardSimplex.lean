-- Prove2me | Theorems.Thm_Ehrhart_SimplexVolume_normalizedVolume_standardSimplex
-- name    : Ehrhart.SimplexVolume.normalizedVolume_standardSimplex
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:46.631058+00:00
-- url     : https://prove2.me/theorems/2d0f8ee8-071d-4652-87e6-d5f7e8c382b4
-- title:
--   Ehrhart.SimplexVolume.normalizedVolume_standardSimplex
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

theorem Ehrhart.SimplexVolume.normalizedVolume_standardSimplex (n : ℕ) :
    normalizedVolume (standardSimplex n) =
      1 / (n.factorial : ℝ) := by sorry
