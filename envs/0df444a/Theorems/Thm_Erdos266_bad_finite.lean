-- Prove2me | Theorems.Thm_Erdos266_bad_finite
-- name    : Erdos266.bad_finite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:36:39.57347+00:00
-- url     : https://prove2.me/theorems/84066e58-7745-53db-8f10-96f5a887d50c
-- title:
--   Erdos266: bad finite
-- statement:
--   The indices at which `a` hits a pole of `f i` form a finite set.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Reduction.lean#L77-L89
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Reduction.lean#L77-L89

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Glue
public import Definitions.Def_Erdos266_Reduction
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
variable {a : ℕ → ℕ}

theorem Erdos266.bad_finite (ha : StrictMono a) (i : ℕ) :
    {n : ℕ | ∃ j ∈ range i, (a n : ℚ) + tSeq j = 0}.Finite := by sorry
