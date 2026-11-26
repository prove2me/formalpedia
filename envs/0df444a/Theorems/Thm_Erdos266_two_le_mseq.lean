-- Prove2me | Theorems.Thm_Erdos266_two_le_mseq
-- name    : Erdos266.two_le_mseq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:47:51.30064+00:00
-- url     : https://prove2.me/theorems/3cc09c45-8d32-46cd-8df2-d081674823c9
-- title:
--   Erdos266: two le mseq
-- statement:
--   The Erdos266 construction uses the two le mseq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Algorithm.lean#L104-L107
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Algorithm.lean#L104-L107

module
public import Definitions.Def_Erdos266_LatticeLemma
public import Definitions.Def_Erdos266_Growth
public import Definitions.Def_Erdos266_Algorithm
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.two_le_mseq (d : ℕ) : 2 ≤ mseq d := by sorry
