-- Prove2me | Theorems.Thm_Erdos266_kOf_le_of_lt
-- name    : Erdos266.kOf_le_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:58:05.071708+00:00
-- url     : https://prove2.me/theorems/0703948a-41bf-5760-adeb-b8efcf2171af
-- title:
--   Erdos266: k Of le of lt
-- statement:
--   The Erdos266 construction uses the k Of le of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L179-L180
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L179-L180

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology

theorem Erdos266.kOf_le_of_lt {n k : ℕ} (h : n < cnt (k + 1)) : kOf n ≤ k := by sorry
