-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE01_iff_hasDegLE
-- name    : AaronsonAmbainis.Bridge.hasDegreeLE01_iff_hasDegLE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:48:33.641072+00:00
-- url     : https://prove2.me/theorems/b3fe18fc-e9ff-438d-8149-64fd9cff5a0e
-- title:
--   Bridge: has Degree LE01 iff has Deg LE
-- statement:
--   The Bridge construction uses the has Degree LE01 iff has Deg LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/ZeroOne.lean#L35-L37
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/ZeroOne.lean#L35-L37

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_ZeroOne
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.hasDegreeLE01_iff_hasDegLE {f : Cube ι → ℝ} {d : ℕ} :
    HasDegreeLE01 f d ↔ HasDegLE (fun b => if b then (1 : ℝ) else 0) f d := by sorry
