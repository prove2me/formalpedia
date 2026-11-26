-- Prove2me | Theorems.Thm_Erdos266_summable_blockAnchor
-- name    : Erdos266.summable_blockAnchor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:48:50.233339+00:00
-- url     : https://prove2.me/theorems/a38658bc-629d-5320-aef2-748398bb0df8
-- title:
--   Erdos266: summable block Anchor
-- statement:
--   The block anchors are summable in the block index.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Algorithm.lean#L239-L286
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Algorithm.lean#L239-L286

module
public import Definitions.Def_Erdos266_LatticeLemma
public import Definitions.Def_Erdos266_Growth
public import Definitions.Def_Erdos266_Algorithm
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.summable_blockAnchor {i : ℕ} (hi : 1 ≤ i) :
    Summable (fun l => blockAnchor i l) := by sorry
