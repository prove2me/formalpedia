-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_rowBoundFin_of_rowBound
-- name    : AaronsonAmbainis.Bridge.rowBoundFin_of_rowBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:49:22.554379+00:00
-- url     : https://prove2.me/theorems/937445da-dda7-42f3-8142-bb3d3e11a656
-- title:
--   Bridge: row Bound Fin of row Bound
-- statement:
--   The Bridge construction uses the row Bound Fin of row Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Transport.lean#L84-L85
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Transport.lean#L84-L85

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Transport
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem AaronsonAmbainis.Bridge.rowBoundFin_of_rowBound (h : RowBound) : RowBoundFin := by sorry
