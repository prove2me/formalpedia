-- Prove2me | Theorems.Thm_Erdos266_tendsto_cast_atTop
-- name    : Erdos266.tendsto_cast_atTop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:37:43.185438+00:00
-- url     : https://prove2.me/theorems/bbd1f5b4-48e4-5982-84b6-246a3347d815
-- title:
--   Erdos266: tendsto cast at Top
-- statement:
--   Strictly increasing sequences of naturals tend to infinity (as reals).
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Reduction.lean#L42-L45
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Reduction.lean#L42-L45

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

theorem Erdos266.tendsto_cast_atTop (ha : StrictMono a) :
    Filter.Tendsto (fun n => (a n : ℝ)) Filter.atTop Filter.atTop := by sorry
