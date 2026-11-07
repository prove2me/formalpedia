-- Prove2me | Theorems.Thm_AaronsonAmbainis_rowBoundPM_of_packing
-- name    : AaronsonAmbainis.rowBoundPM_of_packing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:45:57.156195+00:00
-- url     : https://prove2.me/theorems/6ee59110-92e6-41e1-a4f5-e2c1044875c7
-- title:
--   Aaronson Ambainis: row Bound PM of packing
-- statement:
--   The Aaronson Ambainis construction uses the row Bound PM of packing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Row.lean#L13-L14
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Row.lean#L13-L14

import Definitions.Def_AaronsonAmbainis_Dual_RowAux
import Definitions.Def_AaronsonAmbainis_Dual_Cover
import Definitions.Def_AaronsonAmbainis_Dual_Row
set_option autoImplicit true
open AaronsonAmbainis

theorem AaronsonAmbainis.rowBoundPM_of_packing : PackingBound → RowBoundPM := by sorry
