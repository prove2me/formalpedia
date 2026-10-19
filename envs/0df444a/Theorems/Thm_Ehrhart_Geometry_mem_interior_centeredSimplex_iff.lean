-- Prove2me | Theorems.Thm_Ehrhart_Geometry_mem_interior_centeredSimplex_iff
-- name    : Ehrhart.Geometry.mem_interior_centeredSimplex_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:46.631058+00:00
-- url     : https://prove2.me/theorems/c1797c01-fc85-4bbf-9bfb-497383fed18b
-- title:
--   Ehrhart.Geometry.mem_interior_centeredSimplex_iff
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
open Ehrhart.Geometry
open Set MeasureTheory
open scoped BigOperators

theorem Ehrhart.Geometry.mem_interior_centeredSimplex_iff {n : ℕ} (hn : 0 < n)
    {x : Space n} :
    x ∈ interior (centeredSimplex n) ↔
      (∀ i, -(1 : ℝ) < x i) ∧ (∑ i, x i) < 1 := by sorry
