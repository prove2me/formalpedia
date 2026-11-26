-- Prove2me | Theorems.Thm_AME125_toZ_combineFirst_eq
-- name    : AME125.toZ_combineFirst_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:03:55.499833+00:00
-- url     : https://prove2.me/theorems/1e0e73f2-f1e1-471f-a2a5-26e7a79f31ef
-- title:
--   AME125: to Z combine First eq
-- statement:
--   Changing the kept levels from `b` to `a` adds the difference, extended by zero.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L183-L188
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L183-L188

module
public import Definitions.Def_AME125_Defs
public import Definitions.Def_AME125_GraphState
set_option autoImplicit false
@[expose] public section
public section
open AME125
open OpenQuantumProblem35
open scoped Matrix

theorem AME125.toZ_combineFirst_eq {n m : ℕ} (hm : m ≤ n) (a b : Config m 5) (z : Config (n - m) 5) :
    toZ (combineFirst m hm a z) = toZ (combineFirst m hm b z) + lift (toZ a - toZ b) := by sorry
