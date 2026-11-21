-- Prove2me | Theorems.Thm_Eidos_Ergo_Long_sub_eq_ok_iff
-- name    : Eidos.Ergo.Long.sub_eq_ok_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T23:36:06.437636+00:00
-- url     : https://prove2.me/theorems/78c87f13-fcd4-495f-814f-7d6eb6e4d09b
-- title:
--   Long: sub eq ok iff
-- statement:
--   The Long construction uses the sub eq ok iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Lithos-Protocol/Eidos/blob/071bed01e6e82abd0e5cc1de4bbbc1e2c9e197e4/Eidos/Ergo/Long.lean#L39-L41
-- source:
--   https://github.com/Lithos-Protocol/Eidos/blob/071bed01e6e82abd0e5cc1de4bbbc1e2c9e197e4/Eidos/Ergo/Long.lean#L39-L41

import Std
import Definitions.Def_Eidos_Ergo_Long
set_option autoImplicit false
open Eidos Eidos.Ergo
open Eidos.Ergo.Long

theorem Eidos.Ergo.Long.sub_eq_ok_iff (x y z : Long) :
    sub x y = .ok z ↔ x.val - y.val = z.val := by sorry
