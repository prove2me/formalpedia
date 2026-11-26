-- Prove2me | Theorems.Thm_Erdos266_cross_block
-- name    : Erdos266.cross_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:43:31.660865+00:00
-- url     : https://prove2.me/theorems/d695ca71-c1c4-5484-a496-65066515c5df
-- title:
--   Erdos266: cross block
-- statement:
--   Cross-block separation: everything in block `k` (at most `k·N k + M k`)
--   is strictly below everything in block `k+1` (at least `N (k+1) - M (k+1)`).
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Growth.lean#L107-L122
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Growth.lean#L107-L122

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Growth
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.cross_block {k : ℕ} (hk : 2 ≤ k) :
    k * bigN k + bigM k + bigM (k + 1) < bigN (k + 1) := by sorry
