-- Prove2me | Theorems.Thm_AaronsonAmbainis_Dual_packingBound_iff_rowBoundPM
-- name    : AaronsonAmbainis.Dual.packingBound_iff_rowBoundPM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:27:22.43301+00:00
-- url     : https://prove2.me/theorems/05fea479-b54c-4509-8b8b-3c29495f3766
-- title:
--   Dual: packing Bound iff row Bound PM
-- statement:
--   `PackingBound` and `RowBoundPM` are equivalent.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Sanity.lean#L78-L80
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Sanity.lean#L78-L80

import Definitions.Def_AaronsonAmbainis_Dual_Cover
import Definitions.Def_AaronsonAmbainis_Dual_RowAux
import Definitions.Def_AaronsonAmbainis_MainTheorem
import Definitions.Def_AaronsonAmbainis_Dual_Sanity
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset

theorem AaronsonAmbainis.Dual.packingBound_iff_rowBoundPM : PackingBound ↔ RowBoundPM := by sorry
