-- Prove2me | Theorems.Thm_BoundaryBumping_exists_subcontinuum_meeting_frontier
-- name    : BoundaryBumping.exists_subcontinuum_meeting_frontier
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:51:08.791086+00:00
-- url     : https://prove2.me/theorems/77e32eff-903a-5bc5-a92f-5dfa0deda886
-- title:
--   Boundary Bumping: exists subcontinuum meeting frontier
-- statement:
--   A proper closed subset of a continuum contains, through each of its points,
--   a compact connected subset that meets the frontier of the closed subset.
--
--   Source: https://github.com/Arthur742Ramos/boundary-bumping-lean/blob/58831416a12f73312ac01cdaec19c060a6d4b142/Solution.lean#L104-L113
-- source:
--   https://github.com/Arthur742Ramos/boundary-bumping-lean/blob/58831416a12f73312ac01cdaec19c060a6d4b142/Solution.lean#L104-L113

module
public import Mathlib.Topology.Separation.Regular
public import Definitions.Def_BoundaryBumping_Solution
set_option autoImplicit true
@[expose] public section
public section
open Set
open BoundaryBumping
variable {X : Type*} [TopologicalSpace X]

theorem BoundaryBumping.exists_subcontinuum_meeting_frontier [CompactSpace X] [T2Space X] [ConnectedSpace X]
    {F : Set X} (hF : IsClosed F) (hproper : F ≠ univ) {x : X} (hx : x ∈ F) :
    ∃ K : Set X, IsCompact K ∧ IsConnected K ∧ x ∈ K ∧ K ⊆ F ∧
      (K ∩ frontier F).Nonempty := by sorry
