-- Prove2me | Theorems.Thm_Erdos266_aSeq_strictMono
-- name    : Erdos266.aSeq_strictMono
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T03:02:32.149545+00:00
-- url     : https://prove2.me/theorems/250c2a06-395f-4530-a7b4-100f354dbaae
-- title:
--   Erdos266: a Seq strict Mono
-- statement:
--   **The sequence is strictly monotone.**
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L289-L317
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L289-L317

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology

theorem Erdos266.aSeq_strictMono : StrictMono aSeq := by sorry
