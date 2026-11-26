-- Prove2me | Theorems.Thm_Erdos266_summable_shift
-- name    : Erdos266.summable_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:37:49.392377+00:00
-- url     : https://prove2.me/theorems/7688a779-6f8a-5097-a83e-a026e81765c3
-- title:
--   Erdos266: summable shift
-- statement:
--   Summability survives a constant shift of the denominators.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Reduction.lean#L48-L74
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Reduction.lean#L48-L74

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

theorem Erdos266.summable_shift (ha : StrictMono a)
    (hsum : Summable fun n => ((a n : ℝ))⁻¹) (c : ℝ) :
    Summable fun n => ((a n : ℝ) + c)⁻¹ := by sorry
