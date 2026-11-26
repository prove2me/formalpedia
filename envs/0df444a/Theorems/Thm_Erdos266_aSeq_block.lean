-- Prove2me | Theorems.Thm_Erdos266_aSeq_block
-- name    : Erdos266.aSeq_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:01:48.985066+00:00
-- url     : https://prove2.me/theorems/9bb3f97e-44b3-479a-8e86-a9b982ca7914
-- title:
--   Erdos266: a Seq block
-- statement:
--   The sequence element at position `cnt k + j` is the block-`k` sample.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L322-L332
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L322-L332

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology

theorem Erdos266.aSeq_block {k j : ℕ} (hj : j < dOf k) :
    ((aSeq (cnt k + j) : ℕ) : ℝ) = elemR Sinf k j := by sorry
