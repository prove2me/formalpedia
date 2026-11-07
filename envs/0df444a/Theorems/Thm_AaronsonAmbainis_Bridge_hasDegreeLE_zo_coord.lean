-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_zo_coord
-- name    : AaronsonAmbainis.Bridge.hasDegreeLE_zo_coord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:06:31.38684+00:00
-- url     : https://prove2.me/theorems/796ee5f4-4e1d-4237-828c-6a319ca91ad9
-- title:
--   Bridge: has Degree LE zo coord
-- statement:
--   The `0/1` coordinate function has degree at most `1`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Algebra.lean#L130-L138
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Algebra.lean#L130-L138

import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
import Definitions.Def_AaronsonAmbainis_Bridge_Algebra
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.hasDegreeLE_zo_coord (i : ι) :
    HasDegreeLE (fun x : Cube ι => if x i then (1 : ℝ) else 0) 1 := by sorry
