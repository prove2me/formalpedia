-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_cube_le_iff_mul_sqrt_le
-- name    : AaronsonAmbainis.Level.cube_le_iff_mul_sqrt_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:57:27.904607+00:00
-- url     : https://prove2.me/theorems/03440aac-1068-47dc-a461-a1855a7bccf8
-- title:
--   Level: cube le iff mul sqrt le
-- statement:
--   For `V, L ≥ 0`: `V^3 ≤ 36 K^4 L²` if and only if `V^{3/2} ≤ 6 K² L`, where `V^{3/2}` is written
--   `V · √V`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Increments.lean#L133-L149
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Increments.lean#L133-L149

import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Level_Median
import Definitions.Def_AaronsonAmbainis_Level_ThirdMoment
import Definitions.Def_AaronsonAmbainis_Level_Increments
set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Level
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Level.cube_le_iff_mul_sqrt_le {V K L : ℝ} (hV : 0 ≤ V) (hL : 0 ≤ L) :
    V ^ 3 ≤ 36 * K ^ 4 * L ^ 2 ↔ V * Real.sqrt V ≤ 6 * K ^ 2 * L := by sorry
