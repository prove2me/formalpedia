-- Prove2me | Theorems.Thm_Erdos266_pickIdx_injective
-- name    : Erdos266.pickIdx_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:33:19.925213+00:00
-- url     : https://prove2.me/theorems/c85097e1-e66f-41db-accd-a2d37dbe2074
-- title:
--   Erdos266: pick Idx injective
-- statement:
--   The Erdos266 construction uses the pick Idx injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Enumeration.lean#L95-L96
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Enumeration.lean#L95-L96

module
public import Mathlib
public import Definitions.Def_Erdos266_Enumeration
set_option autoImplicit false
@[expose] public section
public section
open Erdos266

theorem Erdos266.pickIdx_injective : Function.Injective pickIdx := by sorry
