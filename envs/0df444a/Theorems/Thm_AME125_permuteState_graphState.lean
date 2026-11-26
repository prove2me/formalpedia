-- Prove2me | Theorems.Thm_AME125_permuteState_graphState
-- name    : AME125.permuteState_graphState
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:03:34.824753+00:00
-- url     : https://prove2.me/theorems/a4377862-cb85-4138-b50b-3fd95ae3f02d
-- title:
--   AME125: permute State graph State
-- statement:
--   Permuting the parties of a graph state gives the graph state of the permuted matrix.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L132-L138
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L132-L138

module
public import Definitions.Def_AME125_Defs
public import Definitions.Def_AME125_GraphState
set_option autoImplicit false
@[expose] public section
public section
open AME125
open OpenQuantumProblem35
open scoped Matrix

theorem AME125.permuteState_graphState {n : ℕ} (π : Equiv.Perm (Fin n))
    (U : Matrix (Fin n) (Fin n) (ZMod 5)) :
    permuteState π (graphState U) = graphState (U.submatrix π.symm π.symm) := by sorry
