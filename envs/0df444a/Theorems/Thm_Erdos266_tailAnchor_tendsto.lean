-- Prove2me | Theorems.Thm_Erdos266_tailAnchor_tendsto
-- name    : Erdos266.tailAnchor_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:50:47.621855+00:00
-- url     : https://prove2.me/theorems/aceff2ac-c528-487d-974f-fe77f76cac2e
-- title:
--   Erdos266: tail Anchor tendsto
-- statement:
--   The tails tend to `0`.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Algorithm.lean#L302-L307
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Algorithm.lean#L302-L307

module
public import Definitions.Def_Erdos266_LatticeLemma
public import Definitions.Def_Erdos266_Growth
public import Definitions.Def_Erdos266_Algorithm
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.tailAnchor_tendsto (i : ℕ) :
    Filter.Tendsto (fun k => tailAnchor i k) Filter.atTop (nhds 0) := by sorry
