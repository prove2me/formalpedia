-- Prove2me | Theorems.Thm_AME125_graphState_firstHalf
-- name    : AME125.graphState_firstHalf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:03:58.230224+00:00
-- url     : https://prove2.me/theorems/7ff711e2-f5f9-55ee-8b6e-703fac4db695
-- title:
--   AME125: graph State first Half
-- statement:
--   The first-half reduction of a graph state on an even number of parties is maximally mixed
--   when the cut condition holds for the first half.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L246-L283
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L246-L283

module
public import Definitions.Def_AME125_Defs
public import Definitions.Def_AME125_GraphState
set_option autoImplicit false
@[expose] public section
public section
open AME125
open OpenQuantumProblem35
open scoped Matrix

theorem AME125.graphState_firstHalf {n : ℕ} (hn : Even n) (U : Matrix (Fin n) (Fin n) (ZMod 5))
    (h : CutInj (U + Uᵀ) (firstHalf n (n / 2))) :
    HasMaximallyMixedFirstReduction (n / 2) (Nat.div_le_self n 2) (graphState U) := by sorry
