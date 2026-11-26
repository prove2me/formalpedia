-- Prove2me | Theorems.Thm_Erdos266_exists_round_toward_zero
-- name    : Erdos266.exists_round_toward_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:39:39.645778+00:00
-- url     : https://prove2.me/theorems/be420e9b-7ba0-4296-aa41-e014bf7e0dff
-- title:
--   Erdos266: exists round toward zero
-- statement:
--   Round `u` toward zero to a multiple of `c`: the multiple is within `c`
--   of `u` and no larger than `u` in absolute value.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/LatticeLemma.lean#L50-L94
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/LatticeLemma.lean#L50-L94

module
public import Definitions.Def_Erdos266_SlopeLemma
public import Definitions.Def_Erdos266_LatticeLemma
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Matrix

theorem Erdos266.exists_round_toward_zero (u : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ z : ℤ, |c * z - u| ≤ c ∧ c * |(z : ℝ)| ≤ |u| := by sorry
