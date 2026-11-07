-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_hasDegreeLE_pm_coord
-- name    : AaronsonAmbainis.Bridge.hasDegreeLE_pm_coord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:06:22.779831+00:00
-- url     : https://prove2.me/theorems/860385b1-d9fc-4558-849d-dfaf34c031c4
-- title:
--   Bridge: has Degree LE pm coord
-- statement:
--   The `±1` coordinate function has degree at most `1`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Algebra.lean#L125-L127
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Algebra.lean#L125-L127

import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
import Definitions.Def_AaronsonAmbainis_Bridge_Algebra
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.hasDegreeLE_pm_coord (i : ι) :
    HasDegreeLE (fun x : Cube ι => if x i then (-1 : ℝ) else 1) 1 := by sorry
