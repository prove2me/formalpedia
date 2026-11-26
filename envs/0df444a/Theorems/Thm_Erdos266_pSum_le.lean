-- Prove2me | Theorems.Thm_Erdos266_pSum_le
-- name    : Erdos266.pSum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T03:03:10.634617+00:00
-- url     : https://prove2.me/theorems/a2b2449c-1733-474f-9042-e9077a1d9c9b
-- title:
--   Erdos266: p Sum le
-- statement:
--   Every partial sum beyond the threshold is at most the target.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L503-L507
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L503-L507

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology

theorem Erdos266.pSum_le {i' n : ℕ} (hn : cnt (4 * i' + 4) ≤ n) :
    pSum i' n ≤ ((xinf i' : ℚ) : ℝ) := by sorry
