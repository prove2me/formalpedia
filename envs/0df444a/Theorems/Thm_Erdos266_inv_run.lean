-- Prove2me | Theorems.Thm_Erdos266_inv_run
-- name    : Erdos266.inv_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:55:38.810293+00:00
-- url     : https://prove2.me/theorems/91cb974a-fc6a-4629-8b21-98af2342de92
-- title:
--   Erdos266: inv run
-- statement:
--   **The invariant holds along the whole run.**
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Recursion.lean#L287-L296
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Recursion.lean#L287-L296

module
public import Definitions.Def_Erdos266_Algorithm
public import Definitions.Def_Erdos266_Recursion
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.inv_run (k : ℕ) (hk : 2 ≤ k) : Inv k (run k) := by sorry
