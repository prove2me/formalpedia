-- Prove2me | Theorems.Thm_AME125_card_firstHalf
-- name    : AME125.card_firstHalf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:03:51.909034+00:00
-- url     : https://prove2.me/theorems/bfebbe00-c359-5907-ab37-875a74fae004
-- title:
--   AME125: card first Half
-- statement:
--   The AME125 construction uses the card first Half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L241-L242
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/GraphState.lean#L241-L242

module
public import Definitions.Def_AME125_Defs
public import Definitions.Def_AME125_GraphState
set_option autoImplicit false
@[expose] public section
public section
open AME125
open OpenQuantumProblem35
open scoped Matrix

theorem AME125.card_firstHalf {n m : ℕ} (hm : m ≤ n) : (firstHalf n m).card = m := by sorry
