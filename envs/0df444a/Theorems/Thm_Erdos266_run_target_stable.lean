-- Prove2me | Theorems.Thm_Erdos266_run_target_stable
-- name    : Erdos266.run_target_stable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:00:05.530397+00:00
-- url     : https://prove2.me/theorems/c35ee925-6f8b-4bd4-b506-5a86db0528f3
-- title:
--   Erdos266: run target stable
-- statement:
--   The Erdos266 construction uses the run target stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L65-L72
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L65-L72

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology

theorem Erdos266.run_target_stable {k k' : ℕ} (h2 : 2 ≤ k) (hkk : k ≤ k') {i : ℕ} (hi : i < dOf k) :
    (run k').2 i = (run k).2 i := by sorry
