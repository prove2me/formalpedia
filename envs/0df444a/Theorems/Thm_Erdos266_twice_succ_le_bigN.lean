-- Prove2me | Theorems.Thm_Erdos266_twice_succ_le_bigN
-- name    : Erdos266.twice_succ_le_bigN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:01:05.364798+00:00
-- url     : https://prove2.me/theorems/2f6212bf-b057-58d8-b9c5-85f69198a020
-- title:
--   Erdos266: twice succ le big N
-- statement:
--   Doubling bound extracted from the cross-block estimate.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L239-L246
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L239-L246

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology

theorem Erdos266.twice_succ_le_bigN (k : ℕ) : 2 * (k + 1) * bigN k ≤ bigN (k + 1) := by sorry
