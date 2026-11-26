-- Prove2me | Theorems.Thm_Erdos266_aSeq_cast
-- name    : Erdos266.aSeq_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:57:50.613341+00:00
-- url     : https://prove2.me/theorems/4b2db43b-73bf-4c08-be46-edf0c59d0234
-- title:
--   Erdos266: a Seq cast
-- statement:
--   The Erdos266 construction uses the a Seq cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L230-L231
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L230-L231

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology

theorem Erdos266.aSeq_cast (n : ℕ) : (aSeq n : ℤ) = elemZ (kOf n) (n - cnt (kOf n)) := by sorry
