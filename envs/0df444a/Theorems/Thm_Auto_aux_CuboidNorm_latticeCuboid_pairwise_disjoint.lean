-- Prove2me | Theorems.Thm_Auto_aux_CuboidNorm_latticeCuboid_pairwise_disjoint
-- name    : Auto.aux_CuboidNorm.latticeCuboid_pairwise_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:38:15.303311+00:00
-- url     : https://prove2.me/theorems/10478ac7-ca7f-4f0c-a745-64df0a3e19e9
-- title:
--   aux Cuboid Norm: lattice Cuboid pairwise disjoint
-- statement:
--   The aux Cuboid Norm construction uses the lattice Cuboid pairwise disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1751-L1766
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1751-L1766

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

theorem Auto.aux_CuboidNorm.latticeCuboid_pairwise_disjoint {n : ℕ} {ε : ℝ} (hε : ε ≤ 1)
    {k l : ZVector n} (hkl : k ≠ l) :
    Disjoint (latticeCuboid ε k) (latticeCuboid ε l) := by sorry
