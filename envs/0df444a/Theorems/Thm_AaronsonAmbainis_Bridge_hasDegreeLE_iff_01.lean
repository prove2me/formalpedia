-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_iff_01
-- name    : AaronsonAmbainis.Bridge.hasDegreeLE_iff_01
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:52:51.407269+00:00
-- url     : https://prove2.me/theorems/c93277ef-822a-407e-a4cf-2cd711a9709e
-- title:
--   Bridge: has Degree LE iff 01
-- statement:
--   `HasDegreeLE` (characters) is equivalent to the definition with `0/1` monomials.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/ZeroOne.lean#L73-L79
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/ZeroOne.lean#L73-L79

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_ZeroOne
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.hasDegreeLE_iff_01 {f : Cube ι → ℝ} {d : ℕ} : HasDegreeLE f d ↔ HasDegreeLE01 f d := by sorry
