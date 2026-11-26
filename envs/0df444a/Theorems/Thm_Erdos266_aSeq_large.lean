-- Prove2me | Theorems.Thm_Erdos266_aSeq_large
-- name    : Erdos266.aSeq_large
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:02:33.886873+00:00
-- url     : https://prove2.me/theorems/2885e019-5b30-561f-bbce-e5d91618e793
-- title:
--   Erdos266: a Seq large
-- statement:
--   Beyond the threshold block the sequence values dominate `2(i'+1)`.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L441-L454
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L441-L454

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology

theorem Erdos266.aSeq_large {i' m : ℕ} (hm : cnt (4 * i' + 4) ≤ m) :
    (2 * (i' + 1) : ℝ) ≤ ((aSeq m : ℕ) : ℝ) := by sorry
