-- Prove2me | Theorems.Thm_Erdos266_dOf_mono
-- name    : Erdos266.dOf_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:50:24.12224+00:00
-- url     : https://prove2.me/theorems/255b6b50-07cd-4a36-9bea-fd5d4ed4bf4a
-- title:
--   Erdos266: d Of mono
-- statement:
--   The Erdos266 construction uses the d Of mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Algorithm.lean#L160-L169
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Algorithm.lean#L160-L169

module
public import Definitions.Def_Erdos266_LatticeLemma
public import Definitions.Def_Erdos266_Growth
public import Definitions.Def_Erdos266_Algorithm
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.dOf_mono : Monotone dOf := by sorry
