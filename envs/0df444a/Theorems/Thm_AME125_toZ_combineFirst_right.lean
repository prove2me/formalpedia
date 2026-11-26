-- Prove2me | Theorems.Thm_AME125_toZ_combineFirst_right
-- name    : AME125.toZ_combineFirst_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:03:38.041821+00:00
-- url     : https://prove2.me/theorems/338359d8-67ed-5b74-8fec-ba95a5120f1b
-- title:
--   AME125: to Z combine First right
-- statement:
--   The AME125 construction uses the to Z combine First right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L172-L174
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L172-L174

module
public import Definitions.Def_AME125_Defs
public import Definitions.Def_AME125_GraphState
set_option autoImplicit false
@[expose] public section
public section
open AME125
open OpenQuantumProblem35
open scoped Matrix

theorem AME125.toZ_combineFirst_right {n m : ℕ} (hm : m ≤ n) (a : Config m 5) (z : Config (n - m) 5)
    (j : Fin (n - m)) : toZ (combineFirst m hm a z) (rightIndex hm j) = toZ z j := by sorry
