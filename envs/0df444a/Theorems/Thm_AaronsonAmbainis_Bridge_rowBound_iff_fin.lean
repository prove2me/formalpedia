-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_rowBound_iff_fin
-- name    : AaronsonAmbainis.Bridge.rowBound_iff_fin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:52:18.957829+00:00
-- url     : https://prove2.me/theorems/55a48c03-dea0-44b2-b35c-fac62915343f
-- title:
--   Bridge: row Bound iff fin
-- statement:
--   `RowBound` is equivalent to its restriction to the index types `Fin n`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Transport.lean#L88-L89
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Transport.lean#L88-L89

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Transport
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem AaronsonAmbainis.Bridge.rowBound_iff_fin : RowBound ↔ RowBoundFin := by sorry
