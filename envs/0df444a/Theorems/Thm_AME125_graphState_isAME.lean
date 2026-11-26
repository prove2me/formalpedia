-- Prove2me | Theorems.Thm_AME125_graphState_isAME
-- name    : AME125.graphState_isAME
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:04:20.539829+00:00
-- url     : https://prove2.me/theorems/7e8ac7e6-9b37-4732-9a20-b5bd964f911e
-- title:
--   AME125: graph State is AME
-- statement:
--   **A graph state over `ZMod 5` on an even number of parties is AME** when, for every set `A`
--   of half the parties, the block of `U + Uᵀ` between `A` and the rest is injective.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L287-L297
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L287-L297

module
public import Definitions.Def_AME125_Defs
public import Definitions.Def_AME125_GraphState
set_option autoImplicit false
@[expose] public section
public section
open AME125
open OpenQuantumProblem35
open scoped Matrix

theorem AME125.graphState_isAME {n : ℕ} (hn : Even n) (U : Matrix (Fin n) (Fin n) (ZMod 5))
    (h : ∀ A : Finset (Fin n), A.card = n / 2 → CutInj (U + Uᵀ) A) : IsAME (graphState U) := by sorry
