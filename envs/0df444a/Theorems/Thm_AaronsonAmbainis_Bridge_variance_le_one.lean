-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_variance_le_one
-- name    : AaronsonAmbainis.Bridge.variance_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:52:35.226617+00:00
-- url     : https://prove2.me/theorems/2eb7bc28-80ef-441a-b5b3-c3db452ccb24
-- title:
--   Bridge: variance le one
-- statement:
--   A `[-1,1]`-valued function has variance at most `1`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Affine.lean#L83-L94
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Affine.lean#L83-L94

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.variance_le_one {f : Cube ι → ℝ} (h : ∀ x, |f x| ≤ 1) : variance f ≤ 1 := by sorry
