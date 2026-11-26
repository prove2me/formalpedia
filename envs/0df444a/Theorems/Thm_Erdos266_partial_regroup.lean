-- Prove2me | Theorems.Thm_Erdos266_partial_regroup
-- name    : Erdos266.partial_regroup
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T03:01:55.130865+00:00
-- url     : https://prove2.me/theorems/18553850-9883-582b-9197-06f5222b80f5
-- title:
--   Erdos266: partial regroup
-- statement:
--   Partial sums of the series at block boundaries are the `finSum`s.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L335-L343
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L335-L343

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology

theorem Erdos266.partial_regroup (i' k : ℕ) :
    ∑ n ∈ range (cnt k), f (i' + 1) ((aSeq n : ℕ) : ℝ) = finSum i' k Sinf := by sorry
