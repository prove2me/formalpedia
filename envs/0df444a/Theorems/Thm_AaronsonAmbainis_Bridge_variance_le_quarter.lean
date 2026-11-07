-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_variance_le_quarter
-- name    : AaronsonAmbainis.Bridge.variance_le_quarter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:52:29.504194+00:00
-- url     : https://prove2.me/theorems/380f5dd5-ae28-4c37-bca6-ca92d84c03d3
-- title:
--   Bridge: variance le quarter
-- statement:
--   A `[0,1]`-valued function has variance at most `1/4`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Affine.lean#L70-L80
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Affine.lean#L70-L80

import Definitions.Def_AaronsonAmbainis_Bridge_Basic
import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Bridge_Affine
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Bridge.variance_le_quarter {P : Cube ι → ℝ} (h : ∀ x, 0 ≤ P x ∧ P x ≤ 1) :
    variance P ≤ 1 / 4 := by sorry
