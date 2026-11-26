-- Prove2me | Theorems.Thm_Erdos266_succ_le_two_pow
-- name    : Erdos266.succ_le_two_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:39:21.389111+00:00
-- url     : https://prove2.me/theorems/d2edd9a9-1c6a-5173-b07e-b91fe22443af
-- title:
--   Erdos266: succ le two pow
-- statement:
--   `2^k` dominates `k+1`.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Growth.lean#L70-L70
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Growth.lean#L70-L70

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Growth
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.succ_le_two_pow (k : ℕ) : k + 1 ≤ 2 ^ k := by sorry
