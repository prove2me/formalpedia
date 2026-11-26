-- Prove2me | Theorems.Thm_Erdos266_le_dOf
-- name    : Erdos266.le_dOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:47:13.930246+00:00
-- url     : https://prove2.me/theorems/5a64c1f7-f9cf-5d86-98b7-88de8d52763f
-- title:
--   Erdos266: le d Of
-- statement:
--   The Erdos266 construction uses the le d Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Algorithm.lean#L136-L139
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Algorithm.lean#L136-L139

module
public import Definitions.Def_Erdos266_LatticeLemma
public import Definitions.Def_Erdos266_Growth
public import Definitions.Def_Erdos266_Algorithm
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.le_dOf {d k : ℕ} (hm : mseq d ≤ k) : d ≤ dOf k := by sorry
