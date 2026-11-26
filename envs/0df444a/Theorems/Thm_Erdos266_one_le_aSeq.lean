-- Prove2me | Theorems.Thm_Erdos266_one_le_aSeq
-- name    : Erdos266.one_le_aSeq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:58:15.234473+00:00
-- url     : https://prove2.me/theorems/c1555b86-8832-55c6-bf55-a07b1535fd33
-- title:
--   Erdos266: one le a Seq
-- statement:
--   The Erdos266 construction uses the one le a Seq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L233-L236
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L233-L236

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology

theorem Erdos266.one_le_aSeq (n : ℕ) : 1 ≤ aSeq n := by sorry
