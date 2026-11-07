-- Prove2me | Theorems.Thm_AaronsonAmbainis_Dual_rowBoundPM_of_rowBound
-- name    : AaronsonAmbainis.Dual.rowBoundPM_of_rowBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:07:15.378119+00:00
-- url     : https://prove2.me/theorems/e333aa77-1966-41e7-a872-3fb929728734
-- title:
--   Dual: row Bound PM of row Bound
-- statement:
--   The row bound of Agarwal and Ben-David (the hypothesis `RowBound`) implies `RowBoundPM`: it
--   gives rows of cost at most `π² d² / 2 ≤ π² d²` (`rows_of_rowBound`).
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Sanity.lean#L84-L88
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Dual/Sanity.lean#L84-L88

import Definitions.Def_AaronsonAmbainis_Dual_Cover
import Definitions.Def_AaronsonAmbainis_Dual_RowAux
import Definitions.Def_AaronsonAmbainis_MainTheorem
import Definitions.Def_AaronsonAmbainis_Dual_Sanity
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Dual
open Finset

theorem AaronsonAmbainis.Dual.rowBoundPM_of_rowBound : RowBound → RowBoundPM := by sorry
