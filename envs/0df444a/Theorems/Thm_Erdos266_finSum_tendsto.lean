-- Prove2me | Theorems.Thm_Erdos266_finSum_tendsto
-- name    : Erdos266.finSum_tendsto
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T03:02:28.086799+00:00
-- url     : https://prove2.me/theorems/ed240445-1ceb-43ef-af8e-7853599a57bf
-- title:
--   Erdos266: fin Sum tendsto
-- statement:
--   **The block partial sums converge to the targets.**
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L394-L430
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L394-L430

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology

theorem Erdos266.finSum_tendsto (i' : ℕ) :
    Tendsto (fun k => finSum i' k Sinf) atTop (𝓝 ((xinf i' : ℚ) : ℝ)) := by sorry
