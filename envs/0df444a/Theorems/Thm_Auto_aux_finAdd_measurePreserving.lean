-- Prove2me | Theorems.Thm_Auto_aux_finAdd_measurePreserving
-- name    : Auto.aux_finAdd_measurePreserving
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:44:35.462858+00:00
-- url     : https://prove2.me/theorems/4deef658-765d-5c19-a166-8ba42f55cb65
-- title:
--   Auto: aux fin Add measure Preserving
-- statement:
--   The canonical splitting of Euclidean coordinates into two blocks preserves Lebesgue volume.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2199-L2216
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/WienerSpace.lean#L2199-L2216

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_WienerSpace
set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Metric Set Filter Topology
open scoped BigOperators ENNReal Function

theorem Auto.aux_finAdd_measurePreserving (n m : ℕ) :
    MeasurePreserving (EuclideanSpace.finAddEquivProd :
      EuclideanSpace ℝ (Fin (n + m)) →
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m)) := by sorry
