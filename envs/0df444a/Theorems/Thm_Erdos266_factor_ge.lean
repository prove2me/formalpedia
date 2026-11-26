-- Prove2me | Theorems.Thm_Erdos266_factor_ge
-- name    : Erdos266.factor_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:39:36.975192+00:00
-- url     : https://prove2.me/theorems/91231b07-861a-5766-bbb4-4fba79484cd0
-- title:
--   Erdos266: factor ge
-- statement:
--   For `x ≥ 2i` every factor of `f i x` is at least `x/2`.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Growth.lean#L253-L261
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Growth.lean#L253-L261

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Growth
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.factor_ge {i j : ℕ} (hj : j ∈ range i) {x : ℝ} (hx : (2 * i : ℝ) ≤ x) :
    x / 2 ≤ x + (tSeq j : ℝ) := by sorry
