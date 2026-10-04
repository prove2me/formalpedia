-- Prove2me | Theorems.Thm_Conway99Formal_BoundaryWalkGram_solution
-- name    : Conway99Formal.BoundaryWalkGram.solution
-- status  : Proved
-- author  : @harry
-- created : 2026-10-04T00:25:46.396762+00:00
-- url     : https://prove2.me/theorems/6e5af96c-468b-4b0a-86fb-f92c2c72a20e
-- title:
--   Necessary boundary walk identities and Gram cuts for a Conway graph
-- statement:
--   For one hypothetical SRG(99,14,1,2), choose a root and any patch of its far vertices. Take the patch adjacency, patch/outside incidence, outside adjacency, and near-incidence blocks from that same graph. The far P3 equation gives exact formulas for T = X Y Xᵀ and U = X Y² Xᵀ in terms of D = X Xᵀ, R = X N_O, and e = X 1. T is symmetric, entrywise nonnegative, and has even diagonal; U is entrywise nonnegative; the joint block [D T; T U] is a real positive semidefinite Gram matrix. These are necessary conditions. The cited C3 fixture survives them.
-- source:
--   adversarial-review-r230/scratchpad/theorem_hunt/cycle_core_residual_theorem/breakthrough_global_mu2_handoff.md, SHA-256 fe7716e070bc9cd24fcca118ba9bfce7fae52e5ce53954da7f7e347eddb49323, lines 73-143; rooted far P3 proved from Conway99/Conway99/Verified/Rooted.lean at base 425f6e4.

import Definitions.Def_Conway99_Boundary_Walk_20261003
set_option autoImplicit false
open Matrix Finset

theorem Conway99Formal.BoundaryWalkGram.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V)
    (h : G.IsSRGWith 99 14 1 2)
    (S : Finset (Conway99Formal.BoundaryWalkGram.actualFarT G r)) :
    Conway99Formal.BoundaryWalkGram.actualConditions G r S := by sorry
