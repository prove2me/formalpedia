-- Prove2me | Theorems.Thm_Erdos266_rationalShifts_of_f_sums
-- name    : Erdos266.rationalShifts_of_f_sums
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:37:38.354288+00:00
-- url     : https://prove2.me/theorems/ed4b73d6-81c7-5301-a436-df6be12dd26c
-- title:
--   Erdos266: rational Shifts of f sums
-- statement:
--   **The reduction.**  A strictly increasing sequence of naturals with
--   rational `f`-sums has all its shifted Ahmes series rational.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Reduction.lean#L191-L198
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Reduction.lean#L191-L198

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

theorem Erdos266.rationalShifts_of_f_sums (ha : StrictMono a)
    (hf : ∀ i, 1 ≤ i → ∃ q : ℚ, HasSum (fun n => f i (a n)) (q : ℝ)) :
    RationalShifts a := by sorry
