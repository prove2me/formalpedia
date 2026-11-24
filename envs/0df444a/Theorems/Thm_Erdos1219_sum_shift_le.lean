-- Prove2me | Theorems.Thm_Erdos1219_sum_shift_le
-- name    : Erdos1219.sum_shift_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:41:36.778299+00:00
-- url     : https://prove2.me/theorems/a1d1413c-0f26-4de3-accc-01b2fdd7e576
-- title:
--   Erdos1219: sum shift le
-- statement:
--   The shift of an `ℕ`-indexed family has a smaller sum.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/CardinalLemmas.lean#L66-L76
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/CardinalLemmas.lean#L66-L76

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas
set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u

theorem Erdos1219.sum_shift_le (a : ℕ → Cardinal.{u}) :
    Cardinal.sum (fun k => a (k + 1)) ≤ Cardinal.sum a := by sorry
