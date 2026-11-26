-- Prove2me | Theorems.Thm_Erdos266_le_kOf_of_cnt_le
-- name    : Erdos266.le_kOf_of_cnt_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:57:36.139241+00:00
-- url     : https://prove2.me/theorems/6030a308-7740-4a90-855d-a16c132162b1
-- title:
--   Erdos266: le k Of of cnt le
-- statement:
--   The Erdos266 construction uses the le k Of of cnt le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L182-L188
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L182-L188

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology

theorem Erdos266.le_kOf_of_cnt_le {n k : ℕ} (h : cnt k ≤ n) : k ≤ kOf n := by sorry
