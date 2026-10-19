-- Prove2me | Theorems.Thm_Ehrhart_BergmanGeodesicConvexity_exponentialMoment_sq_le_partition_mul_second
-- name    : Ehrhart.BergmanGeodesicConvexity.exponentialMoment_sq_le_partition_mul_second
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:54:44.97552+00:00
-- url     : https://prove2.me/theorems/ae6e604b-4dfa-4a4c-967a-fbd53b05fd49
-- title:
--   Ehrhart.BergmanGeodesicConvexity.exponentialMoment_sq_le_partition_mul_second
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
open Ehrhart.BergmanGeodesicConvexity
open Set Module
open scoped BigOperators InnerProductSpace

theorem Ehrhart.BergmanGeodesicConvexity.exponentialMoment_sq_le_partition_mul_second
    {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (order : ι → ℕ)
    (hw : ∀ i, 0 ≤ w i) (t : ℝ) :
    exponentialMoment w order 1 t ^ 2 ≤
      exponentialPartition w order t *
        exponentialMoment w order 2 t := by sorry
