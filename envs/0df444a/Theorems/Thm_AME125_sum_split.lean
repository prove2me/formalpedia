-- Prove2me | Theorems.Thm_AME125_sum_split
-- name    : AME125.sum_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:03:14.392031+00:00
-- url     : https://prove2.me/theorems/55ccb35a-7544-41dc-b33f-dee7bc6f6471
-- title:
--   AME125: sum split
-- statement:
--   A sum over `Fin n` splits into the first `m` indices and the last `n - m`.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L101-L105
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L101-L105

module
public import Definitions.Def_AME125_Defs
public import Definitions.Def_AME125_GraphState
set_option autoImplicit false
@[expose] public section
public section
open AME125
open OpenQuantumProblem35
open scoped Matrix

theorem AME125.sum_split {n m : ℕ} (hm : m ≤ n) {M : Type*} [AddCommMonoid M] (f : Fin n → M) :
    ∑ i, f i = ∑ i : Fin m, f (leftIndex hm i) + ∑ j : Fin (n - m), f (rightIndex hm j) := by sorry
