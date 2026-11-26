-- Prove2me | Theorems.Thm_AME125_toZ_combineFirst_apply
-- name    : AME125.toZ_combineFirst_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:03:52.176563+00:00
-- url     : https://prove2.me/theorems/0033a494-2c22-43f9-beea-4b13d9c69df4
-- title:
--   AME125: to Z combine First apply
-- statement:
--   The AME125 construction uses the to Z combine First apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L176-L180
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L176-L180

module
public import Definitions.Def_AME125_Defs
public import Definitions.Def_AME125_GraphState
set_option autoImplicit false
@[expose] public section
public section
open AME125
open OpenQuantumProblem35
open scoped Matrix

theorem AME125.toZ_combineFirst_apply {n m : ℕ} (hm : m ≤ n) (a : Config m 5) (z : Config (n - m) 5)
    (i : Fin n) : toZ (combineFirst m hm a z) i =
      if hi : i.1 < m then toZ a ⟨i.1, hi⟩
      else toZ z ⟨i.1 - m, Nat.sub_lt_sub_right (Nat.le_of_not_lt hi) i.2⟩ := by sorry
