-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_rowBound_iff_printed
-- name    : AaronsonAmbainis.Bridge.rowBound_iff_printed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:22:51.837582+00:00
-- url     : https://prove2.me/theorems/8a02954b-432d-403a-8c3d-3b2d765cdd8a
-- title:
--   Bridge: row Bound iff printed
-- statement:
--   `RowBound` is equivalent to Theorem 1.7 of arXiv:2410.19062 as printed.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedRow.lean#L104-L105
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/PrintedRow.lean#L104-L105

import Definitions.Def_AaronsonAmbainis_Bridge_Poly
import Definitions.Def_AaronsonAmbainis_Bridge_Transport
import Definitions.Def_AaronsonAmbainis_Bridge_ZeroOne
import Definitions.Def_AaronsonAmbainis_Bridge_PrintedRow
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset MvPolynomial

theorem AaronsonAmbainis.Bridge.rowBound_iff_printed : RowBound ↔ FbsDegPrinted := by sorry
