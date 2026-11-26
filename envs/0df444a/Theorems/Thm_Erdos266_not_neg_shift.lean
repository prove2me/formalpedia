-- Prove2me | Theorems.Thm_Erdos266_not_neg_shift
-- name    : Erdos266.not_neg_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:31:25.30981+00:00
-- url     : https://prove2.me/theorems/648210f4-dd22-46c0-bdeb-43c98237c4f7
-- title:
--   Erdos266: not neg shift
-- statement:
--   A sequence of positive integers admits no rational shift equal to `-aₙ`
--   for nonnegative rational `t`.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Glue.lean#L43-L47
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Glue.lean#L43-L47

module
public import Mathlib
public import Definitions.Def_Erdos266_Glue
set_option autoImplicit false
@[expose] public section
public section
open Erdos266

theorem Erdos266.not_neg_shift {a : ℕ → ℕ} (hpos : ∀ n, 1 ≤ a n) {t : ℚ} (ht : 0 ≤ t) :
    ¬ ∃ n : ℕ, t = -(a n) := by sorry
