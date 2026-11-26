-- Prove2me | Theorems.Thm_Erdos266_f_cast
-- name    : Erdos266.f_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:36:52.016424+00:00
-- url     : https://prove2.me/theorems/736362df-495e-4664-95e3-1c05f324ffa6
-- title:
--   Erdos266: f cast
-- statement:
--   Cast bookkeeping: `f i` at `a n` is the cast of an explicit rational.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Reduction.lean#L98-L102
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Reduction.lean#L98-L102

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

theorem Erdos266.f_cast (i n : ℕ) :
    f i ((a n : ℕ) : ℝ)
      = (((∏ k ∈ range i, ((a n : ℚ) + tSeq k))⁻¹ : ℚ) : ℝ) := by sorry
