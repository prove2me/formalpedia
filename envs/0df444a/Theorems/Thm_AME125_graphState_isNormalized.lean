-- Prove2me | Theorems.Thm_AME125_graphState_isNormalized
-- name    : AME125.graphState_isNormalized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:03:11.564739+00:00
-- url     : https://prove2.me/theorems/2be39ab7-f7b2-5e98-a442-048b386531fd
-- title:
--   AME125: graph State is Normalized
-- statement:
--   The graph state is normalised when `n` is even.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L108-L119
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L108-L119

module
public import Definitions.Def_AME125_Defs
public import Definitions.Def_AME125_GraphState
set_option autoImplicit false
@[expose] public section
public section
open AME125
open OpenQuantumProblem35
open scoped Matrix

theorem AME125.graphState_isNormalized {n : ℕ} (hn : Even n) (U : Matrix (Fin n) (Fin n) (ZMod 5)) :
    IsNormalized (graphState U) := by sorry
