-- Prove2me | Theorems.Thm_Erdos266_lt_mseq_succ_dOf
-- name    : Erdos266.lt_mseq_succ_dOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:49:59.950487+00:00
-- url     : https://prove2.me/theorems/839db80e-51fa-430e-8826-a607553a0db4
-- title:
--   Erdos266: lt mseq succ d Of
-- statement:
--   The Erdos266 construction uses the lt mseq succ d Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Algorithm.lean#L141-L145
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Algorithm.lean#L141-L145

module
public import Definitions.Def_Erdos266_LatticeLemma
public import Definitions.Def_Erdos266_Growth
public import Definitions.Def_Erdos266_Algorithm
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.lt_mseq_succ_dOf {k : ℕ} : k < mseq (dOf k + 1) := by sorry
