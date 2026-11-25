-- Prove2me | Theorems.Thm_BoundaryBumping_exists_clopen_between_component_and_open
-- name    : BoundaryBumping.exists_clopen_between_component_and_open
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:51:06.652581+00:00
-- url     : https://prove2.me/theorems/55e07979-0760-54db-887b-8865c6f5d0dd
-- title:
--   Boundary Bumping: exists clopen between component and open
-- statement:
--   An open neighborhood of a component in a compact Hausdorff space contains
--   a clopen neighborhood of the whole component.
--
--   Source: https://github.com/Arthur742Ramos/boundary-bumping-lean/blob/58831416a12f73312ac01cdaec19c060a6d4b142/Solution.lean#L32-L46
-- source:
--   https://github.com/Arthur742Ramos/boundary-bumping-lean/blob/58831416a12f73312ac01cdaec19c060a6d4b142/Solution.lean#L32-L46

module
public import Mathlib.Topology.Separation.Regular
public import Definitions.Def_BoundaryBumping_Solution
set_option autoImplicit true
@[expose] public section
public section
open Set
open BoundaryBumping
variable {X : Type*} [TopologicalSpace X]

theorem BoundaryBumping.exists_clopen_between_component_and_open [CompactSpace X] [T2Space X]
    (x : X) {U : Set X} (hU : IsOpen U) (hCU : connectedComponent x ⊆ U) :
    ∃ V : Set X, IsClopen V ∧ connectedComponent x ⊆ V ∧ V ⊆ U := by sorry
