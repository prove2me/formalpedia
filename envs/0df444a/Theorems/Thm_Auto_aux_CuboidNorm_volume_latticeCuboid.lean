-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_volume_latticeCuboid
-- name    : Auto.aux_CuboidNorm.volume_latticeCuboid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:41:47.089824+00:00
-- url     : https://prove2.me/theorems/8835c86f-fb94-51db-9cf5-2914917611b7
-- title:
--   aux Cuboid Norm: volume lattice Cuboid
-- statement:
--   The aux Cuboid Norm construction uses the volume lattice Cuboid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1744-L1749
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1744-L1749

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
open Auto.aux_CuboidNorm
variable {α κ : Type*} [MeasurableSpace α] [DecidableEq κ]

theorem Auto.aux_CuboidNorm.volume_latticeCuboid {n : ℕ} (ε : ℝ) (k : ZVector n) :
    volume (latticeCuboid ε k) = ∏ _ : Fin n, ENNReal.ofReal ε := by sorry
