-- Prove2me | Theorems.Thm_Erdos266_run_succ
-- name    : Erdos266.run_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:55:28.834931+00:00
-- url     : https://prove2.me/theorems/88e2bd1b-2d7b-5ac7-a717-bbe7f7e76dce
-- title:
--   Erdos266: run succ
-- statement:
--   The Erdos266 construction uses the run succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Recursion.lean#L179-L180
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Recursion.lean#L179-L180

module
public import Definitions.Def_Erdos266_Algorithm
public import Definitions.Def_Erdos266_Recursion
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.run_succ {k : ℕ} (hk : 2 ≤ k) : run (k + 1) = stepSt k (run k) := by sorry
