-- Prove2me | Theorems.Thm_Erdos266_dOf_lt_iff
-- name    : Erdos266.dOf_lt_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:48:19.464036+00:00
-- url     : https://prove2.me/theorems/cc42a183-c0ac-5855-8968-4063db60be7b
-- title:
--   Erdos266: d Of lt iff
-- statement:
--   The Erdos266 construction uses the d Of lt iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Algorithm.lean#L147-L158
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Algorithm.lean#L147-L158

module
public import Definitions.Def_Erdos266_LatticeLemma
public import Definitions.Def_Erdos266_Growth
public import Definitions.Def_Erdos266_Algorithm
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.dOf_lt_iff {d k : ℕ} (hk : 2 ≤ k) : dOf k < d ↔ k < mseq d := by sorry
