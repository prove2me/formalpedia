-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_rowBound_iff_printedML
-- name    : AaronsonAmbainis.Bridge.rowBound_iff_printedML
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:23:22.773582+00:00
-- url     : https://prove2.me/theorems/e7df87a7-9bf1-45ff-85ac-71cb4d7a469f
-- title:
--   Bridge: row Bound iff printed ML
-- statement:
--   `RowBound` is equivalent to the printed theorem in its narrowest reading.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedRow.lean#L108-L109
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedRow.lean#L108-L109

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Transport
import Definitions.Def_AaronsonAmbainis_Bridge_ZeroOne
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedRow
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial

theorem AaronsonAmbainis.Bridge.rowBound_iff_printedML : RowBound ↔ FbsDegPrintedML := by sorry
