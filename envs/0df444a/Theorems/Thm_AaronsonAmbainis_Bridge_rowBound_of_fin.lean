-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_rowBound_of_fin
-- name    : AaronsonAmbainis.Bridge.rowBound_of_fin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:49:28.896624+00:00
-- url     : https://prove2.me/theorems/9d486891-7e33-45a8-93d7-15e0bcb526fb
-- title:
--   Bridge: row Bound of fin
-- statement:
--   The `[n]` statement implies the statement for all finite index types.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Transport.lean#L78-L82
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Transport.lean#L78-L82

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Transport
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem AaronsonAmbainis.Bridge.rowBound_of_fin (h : RowBoundFin) : RowBound := by sorry
