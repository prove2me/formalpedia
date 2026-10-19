-- Prove2me | Theorems.Thm_Ehrhart_SimplexVolume_splitStandardSimplex_fiber_of_mem_Ico
-- name    : Ehrhart.SimplexVolume.splitStandardSimplex_fiber_of_mem_Ico
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:46.631058+00:00
-- url     : https://prove2.me/theorems/4761b822-63ae-4ce9-af61-d60a0a85452b
-- title:
--   Ehrhart.SimplexVolume.splitStandardSimplex_fiber_of_mem_Ico
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

theorem Ehrhart.SimplexVolume.splitStandardSimplex_fiber_of_mem_Ico (n : ℕ) {t : ℝ}
    (ht : t ∈ Set.Ico (0 : ℝ) 1) :
    Prod.mk t ⁻¹' splitStandardSimplex n =
      (1 - t) • standardSimplex n := by sorry
