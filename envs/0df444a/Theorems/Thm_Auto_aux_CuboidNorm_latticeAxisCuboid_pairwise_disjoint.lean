-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_latticeAxisCuboid_pairwise_disjoint
-- name    : Auto.aux_CuboidNorm.latticeAxisCuboid_pairwise_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:37:26.512293+00:00
-- url     : https://prove2.me/theorems/25f583c4-3600-5ea4-977c-8f590f8d755d
-- title:
--   aux Cuboid Norm: lattice Axis Cuboid pairwise disjoint
-- statement:
--   The aux Cuboid Norm construction uses the lattice Axis Cuboid pairwise disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1355-L1387
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1355-L1387

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

theorem Auto.aux_CuboidNorm.latticeAxisCuboid_pairwise_disjoint {n : ℕ}
    {ε δ : ℝ} (hε : ε ≤ 1) (hδ : δ ≤ 1) (i : Fin n)
    {k l : ZVector n} (hkl : k ≠ l) :
    Disjoint (latticeAxisCuboid ε δ i k) (latticeAxisCuboid ε δ i l) := by sorry
