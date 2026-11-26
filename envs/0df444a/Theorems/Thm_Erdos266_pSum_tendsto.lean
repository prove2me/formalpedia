-- Prove2me | Theorems.Thm_Erdos266_pSum_tendsto
-- name    : Erdos266.pSum_tendsto
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:59:04.164476+00:00
-- url     : https://prove2.me/theorems/b655dd37-8c69-4974-871d-e24b215d6f6a
-- title:
--   Erdos266: p Sum tendsto
-- statement:
--   **All partial sums converge to the target.**
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L484-L500
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L484-L500

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology

theorem Erdos266.pSum_tendsto (i' : ℕ) :
    Tendsto (fun n => pSum i' n) atTop (𝓝 ((xinf i' : ℚ) : ℝ)) := by sorry
