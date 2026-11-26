-- Prove2me | Theorems.Thm_Erdos266_shiftTerm_cast
-- name    : Erdos266.shiftTerm_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:38:06.303426+00:00
-- url     : https://prove2.me/theorems/bc1e03c7-74f4-45e8-9ea8-cea1f16e9a34
-- title:
--   Erdos266: shift Term cast
-- statement:
--   Cast bookkeeping: the shifted term is the cast of an explicit rational.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Reduction.lean#L92-L95
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Reduction.lean#L92-L95

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

theorem Erdos266.shiftTerm_cast (n k : ℕ) :
    ((a n : ℝ) + (tSeq k : ℝ))⁻¹ = ((((a n : ℚ) + tSeq k)⁻¹ : ℚ) : ℝ) := by sorry
