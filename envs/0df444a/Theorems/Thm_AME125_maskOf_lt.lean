-- Prove2me | Theorems.Thm_AME125_maskOf_lt
-- name    : AME125.maskOf_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:14:29.983736+00:00
-- url     : https://prove2.me/theorems/53a7d31a-380e-457e-a0b8-b6e47fa15891
-- title:
--   AME125: mask Of lt
-- statement:
--   The AME125 construction uses the mask Of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Certificate.lean#L173-L178
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Certificate.lean#L173-L178

module
public import Definitions.Def_AME125_Data
public import Definitions.Def_AME125_GraphState
public import Definitions.Def_AME125_Certificate
set_option autoImplicit false
@[expose] public section
public section
open AME125
open scoped Matrix

theorem AME125.maskOf_lt (A : Finset (Fin 12)) : maskOf A < 4096 := by sorry
