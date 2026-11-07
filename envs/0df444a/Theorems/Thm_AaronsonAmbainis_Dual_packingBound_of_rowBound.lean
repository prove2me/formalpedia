-- Prove2me | Theorems.Thm_AaronsonAmbainis_Dual_packingBound_of_rowBound
-- name    : AaronsonAmbainis.Dual.packingBound_of_rowBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:27:26.520473+00:00
-- url     : https://prove2.me/theorems/52f06ca8-f236-4e49-b851-020e41273c52
-- title:
--   Dual: packing Bound of row Bound
-- statement:
--   Consequently `PackingBound` follows from the row bound of Agarwal and Ben-David (the
--   hypothesis `RowBound`).
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Sanity.lean#L92-L93
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Sanity.lean#L92-L93

import Definitions.Def_AaronsonAmbainis_Dual_Cover
import Definitions.Def_AaronsonAmbainis_Dual_RowAux
import Definitions.Def_AaronsonAmbainis_MainTheorem
import Definitions.Def_AaronsonAmbainis_Dual_Sanity
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset

theorem AaronsonAmbainis.Dual.packingBound_of_rowBound : RowBound → PackingBound := by sorry
