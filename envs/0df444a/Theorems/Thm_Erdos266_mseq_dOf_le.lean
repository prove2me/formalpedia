-- Prove2me | Theorems.Thm_Erdos266_mseq_dOf_le
-- name    : Erdos266.mseq_dOf_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:47:40.7538+00:00
-- url     : https://prove2.me/theorems/cd8d889f-65ca-4efb-9002-9c1213fbd7d0
-- title:
--   Erdos266: mseq d Of le
-- statement:
--   The Erdos266 construction uses the mseq d Of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Algorithm.lean#L133-L134
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Algorithm.lean#L133-L134

module
public import Definitions.Def_Erdos266_LatticeLemma
public import Definitions.Def_Erdos266_Growth
public import Definitions.Def_Erdos266_Algorithm
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.mseq_dOf_le {k : ℕ} (hk : 2 ≤ k) : mseq (dOf k) ≤ k := by sorry
