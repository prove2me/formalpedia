-- Prove2me | Theorems.Thm_Erdos266_prod_shift_sub
-- name    : Erdos266.prod_shift_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:39:39.716004+00:00
-- url     : https://prove2.me/theorems/3d8f3f07-dd0b-4068-862e-97664f43f680
-- title:
--   Erdos266: prod shift sub
-- statement:
--   The telescoping identity behind the linear term: shifting every factor
--   by `x` changes the product by `x` times a sum of `i` hybrid products.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/SlopeLemma.lean#L98-L145
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/SlopeLemma.lean#L98-L145

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_SlopeLemma
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.prod_shift_sub (i : ℕ) (N x : ℝ) :
    (∏ j ∈ range i, (N + (x + (tSeq j : ℝ)))) - (∏ j ∈ range i, (N + (tSeq j : ℝ)))
      = x * ∑ k ∈ range i, ∏ j ∈ (range i).erase k,
          (N + if j < k then x + (tSeq j : ℝ) else (tSeq j : ℝ)) := by sorry
