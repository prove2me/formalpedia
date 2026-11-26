-- Prove2me | Theorems.Thm_AME125_testBit_maskOf
-- name    : AME125.testBit_maskOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:12:43.866037+00:00
-- url     : https://prove2.me/theorems/6c882772-143e-4e60-8b36-b409216c5665
-- title:
--   AME125: test Bit mask Of
-- statement:
--   The AME125 construction uses the test Bit mask Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Certificate.lean#L168-L171
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Certificate.lean#L168-L171

module
public import Definitions.Def_AME125_Data
public import Definitions.Def_AME125_GraphState
public import Definitions.Def_AME125_Certificate
set_option autoImplicit false
@[expose] public section
public section
open AME125
open scoped Matrix

theorem AME125.testBit_maskOf (A : Finset (Fin 12)) (i : Fin 12) :
    (maskOf A).testBit i.1 = true ↔ i ∈ A := by sorry
