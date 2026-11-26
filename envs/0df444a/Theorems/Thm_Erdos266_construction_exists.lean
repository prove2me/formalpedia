-- Prove2me | Theorems.Thm_Erdos266_construction_exists
-- name    : Erdos266.construction_exists
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T03:03:02.386985+00:00
-- url     : https://prove2.me/theorems/0782e468-5ea7-4d5b-b539-debbfe091e08
-- title:
--   Erdos266: construction exists
-- statement:
--   **The construction exists** — the input the reduction needs.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L540-L545
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L540-L545

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology

theorem Erdos266.construction_exists :
    ∃ a : ℕ → ℕ, StrictMono a ∧ 1 ≤ a 0 ∧
      ∀ i, 1 ≤ i → ∃ q : ℚ, HasSum (fun n => f i (a n)) (q : ℝ) := by sorry
