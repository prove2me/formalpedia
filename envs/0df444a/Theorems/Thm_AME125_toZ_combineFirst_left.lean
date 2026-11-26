-- Prove2me | Theorems.Thm_AME125_toZ_combineFirst_left
-- name    : AME125.toZ_combineFirst_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:03:35.35971+00:00
-- url     : https://prove2.me/theorems/6200a965-46ff-5b5c-a565-329cbbca0079
-- title:
--   AME125: to Z combine First left
-- statement:
--   The AME125 construction uses the to Z combine First left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L168-L170
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L168-L170

module
public import Definitions.Def_AME125_Defs
public import Definitions.Def_AME125_GraphState
set_option autoImplicit false
@[expose] public section
public section
open AME125
open OpenQuantumProblem35
open scoped Matrix

theorem AME125.toZ_combineFirst_left {n m : ℕ} (hm : m ≤ n) (a : Config m 5) (z : Config (n - m) 5)
    (i : Fin m) : toZ (combineFirst m hm a z) (leftIndex hm i) = toZ a i := by sorry
