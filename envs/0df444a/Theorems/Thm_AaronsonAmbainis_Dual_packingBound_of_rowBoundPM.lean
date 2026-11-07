-- Prove2me | Theorems.Thm_AaronsonAmbainis_Dual_packingBound_of_rowBoundPM
-- name    : AaronsonAmbainis.Dual.packingBound_of_rowBoundPM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:05:48.060792+00:00
-- url     : https://prove2.me/theorems/3f3578c2-a214-429a-8a1d-1adb0449e215
-- title:
--   Dual: packing Bound of row Bound PM
-- statement:
--   The converse of `rowBoundPM_of_packing`: rows of cost at most `π² d²` bound every fractional
--   packing.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Sanity.lean#L69-L75
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Sanity.lean#L69-L75

import Definitions.Def_AaronsonAmbainis_Dual_Cover
import Definitions.Def_AaronsonAmbainis_Dual_RowAux
import Definitions.Def_AaronsonAmbainis_MainTheorem
import Definitions.Def_AaronsonAmbainis_Dual_Sanity
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset

theorem AaronsonAmbainis.Dual.packingBound_of_rowBoundPM : RowBoundPM → PackingBound := by sorry
