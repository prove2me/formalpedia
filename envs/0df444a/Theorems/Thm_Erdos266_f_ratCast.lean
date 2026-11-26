-- Prove2me | Theorems.Thm_Erdos266_f_ratCast
-- name    : Erdos266.f_ratCast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:34:12.095718+00:00
-- url     : https://prove2.me/theorems/b7734ac3-9607-537b-b47e-5a066dac500b
-- title:
--   Erdos266: f rat Cast
-- statement:
--   `f` at a rational point is the cast of an explicit rational — the
--   correction terms in the reduction are rational because of this.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Defs.lean#L49-L53
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Defs.lean#L49-L53

module
public import Definitions.Def_Erdos266_Enumeration
public import Definitions.Def_Erdos266_Defs
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.f_ratCast (i : ℕ) (q : ℚ) :
    f i (q : ℝ) = ((∏ j ∈ range i, (q + tSeq j))⁻¹ : ℚ) := by sorry
