-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_iff_hasDegLE
-- name    : AaronsonAmbainis.Bridge.hasDegreeLE_iff_hasDegLE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:48:24.585627+00:00
-- url     : https://prove2.me/theorems/212ae000-d049-4a8c-9f5f-d147faea2bc9
-- title:
--   Bridge: has Degree LE iff has Deg LE
-- statement:
--   The Bridge construction uses the has Degree LE iff has Deg LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/ZeroOne.lean#L30-L32
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/ZeroOne.lean#L30-L32

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_ZeroOne
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.hasDegreeLE_iff_hasDegLE {f : Cube ι → ℝ} {d : ℕ} :
    HasDegreeLE f d ↔ HasDegLE (fun b => if b then (-1 : ℝ) else 1) f d := by sorry
