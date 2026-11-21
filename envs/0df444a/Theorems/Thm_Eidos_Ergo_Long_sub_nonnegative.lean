-- Prove2me | Theorems.Thm_Eidos_Ergo_Long_sub_nonnegative
-- name    : Eidos.Ergo.Long.sub_nonnegative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:36:09.530406+00:00
-- url     : https://prove2.me/theorems/93f7040e-7fbb-484f-ad16-e53bc90af89b
-- title:
--   Long: sub nonnegative
-- statement:
--   A decrease between nonnegative Long values can be computed without overflow.
--
--   Source: https://github.com/Lithos-Protocol/Eidos/blob/071bed01e6e82abd0e5cc1de4bbbc1e2c9e197e4/Eidos/Ergo/Long.lean#L44-L50
-- source:
--   https://github.com/Lithos-Protocol/Eidos/blob/071bed01e6e82abd0e5cc1de4bbbc1e2c9e197e4/Eidos/Ergo/Long.lean#L44-L50

import Std
import Definitions.Def_Eidos_Ergo_Long
set_option autoImplicit false
open Eidos Eidos.Ergo
open Eidos.Ergo.Long

theorem Eidos.Ergo.Long.sub_nonnegative (x y : Long) (hy : 0 ≤ y.val) (hxy : y.val ≤ x.val) :
    ∃ z, sub x y = .ok z ∧ z.val = x.val - y.val ∧ 0 ≤ z.val := by sorry
