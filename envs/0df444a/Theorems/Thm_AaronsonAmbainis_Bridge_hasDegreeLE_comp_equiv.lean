-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_comp_equiv
-- name    : AaronsonAmbainis.Bridge.hasDegreeLE_comp_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:49:06.333693+00:00
-- url     : https://prove2.me/theorems/d56d5a49-154e-4e46-8732-929c9ddf9f85
-- title:
--   Bridge: has Degree LE comp equiv
-- statement:
--   `HasDegreeLE` is invariant under relabelling the coordinates.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Transport.lean#L32-L44
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Transport.lean#L32-L44

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Transport
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
omit [DecidableEq ι] [DecidableEq κ]

theorem AaronsonAmbainis.Bridge.hasDegreeLE_comp_equiv (e : ι ≃ κ) {f : Cube ι → ℝ} {d : ℕ} (h : HasDegreeLE f d) :
    HasDegreeLE (fun y : Cube κ => f (fun i => y (e i))) d := by sorry
