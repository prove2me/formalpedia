-- Prove2me | Theorems.Thm_Ehrhart_Geometry_zero_mem_interior_centeredSimplex
-- name    : Ehrhart.Geometry.zero_mem_interior_centeredSimplex
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:46.631058+00:00
-- url     : https://prove2.me/theorems/d5fc8651-d2ee-469f-869d-c9e0cd1be9a3
-- title:
--   Ehrhart.Geometry.zero_mem_interior_centeredSimplex
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

theorem Ehrhart.Geometry.zero_mem_interior_centeredSimplex (n : ℕ) (hn : 0 < n) :
    (0 : Space n) ∈ interior (centeredSimplex n) := by sorry
