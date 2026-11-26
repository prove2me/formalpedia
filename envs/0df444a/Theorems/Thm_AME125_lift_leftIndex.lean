-- Prove2me | Theorems.Thm_AME125_lift_leftIndex
-- name    : AME125.lift_leftIndex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:03:35.473602+00:00
-- url     : https://prove2.me/theorems/cb92685e-6669-5d9e-b769-89f822e79ba6
-- title:
--   AME125: lift left Index
-- statement:
--   The AME125 construction uses the lift left Index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L164-L166
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L164-L166

module
public import Definitions.Def_AME125_Defs
public import Definitions.Def_AME125_GraphState
set_option autoImplicit false
@[expose] public section
public section
open AME125
open OpenQuantumProblem35
open scoped Matrix

theorem AME125.lift_leftIndex {n m : ℕ} (hm : m ≤ n) (v : Fin m → ZMod 5) (i : Fin m) :
    lift (n := n) v (leftIndex hm i) = v i := by sorry
