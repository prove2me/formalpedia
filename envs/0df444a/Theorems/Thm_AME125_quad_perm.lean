-- Prove2me | Theorems.Thm_AME125_quad_perm
-- name    : AME125.quad_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:03:24.487383+00:00
-- url     : https://prove2.me/theorems/4fd09778-c8ea-46cd-9b88-26a26567ba0a
-- title:
--   AME125: quad perm
-- statement:
--   The quadratic form of a permuted configuration is the form of the permuted matrix.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L122-L129
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L122-L129

module
public import Definitions.Def_AME125_Defs
public import Definitions.Def_AME125_GraphState
set_option autoImplicit false
@[expose] public section
public section
open AME125
open OpenQuantumProblem35
open scoped Matrix

theorem AME125.quad_perm {n : ℕ} (U : Matrix (Fin n) (Fin n) (ZMod 5)) (π : Equiv.Perm (Fin n))
    (x : Fin n → ZMod 5) : quad U (fun i ↦ x (π i)) = quad (U.submatrix π.symm π.symm) x := by sorry
