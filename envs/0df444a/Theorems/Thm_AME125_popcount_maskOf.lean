-- Prove2me | Theorems.Thm_AME125_popcount_maskOf
-- name    : AME125.popcount_maskOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:15:21.405317+00:00
-- url     : https://prove2.me/theorems/87e26c79-70da-43d8-a297-0ff39c24b87d
-- title:
--   AME125: popcount mask Of
-- statement:
--   The AME125 construction uses the popcount mask Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Certificate.lean#L180-L192
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Certificate.lean#L180-L192

module
public import Definitions.Def_AME125_Data
public import Definitions.Def_AME125_GraphState
public import Definitions.Def_AME125_Certificate
set_option autoImplicit false
@[expose] public section
public section
open AME125
open scoped Matrix

theorem AME125.popcount_maskOf (A : Finset (Fin 12)) : popcount (maskOf A) = A.card := by sorry
