-- Prove2me | Theorems.Thm_AaronsonAmbainis_sensitivityBound
-- name    : AaronsonAmbainis.sensitivityBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:13:55.727607+00:00
-- url     : https://prove2.me/theorems/a2cd96d2-48f5-4c2a-9f83-88f6bb3e4e75
-- title:
--   Aaronson Ambainis: sensitivity Bound
-- statement:
--   The sensitivity bound at every point (Corollary 6.10 of the paper), with no hypothesis.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Chain.lean#L90-L90
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Chain.lean#L90-L90

import Definitions.Def_AaronsonAmbainis_DetTheorem
import Definitions.Def_AaronsonAmbainis_TwoSided_Main
import Definitions.Def_AaronsonAmbainis_Level_Main
import Definitions.Def_AaronsonAmbainis_Average_Main
import Definitions.Def_AaronsonAmbainis_Row_Main
import Definitions.Def_AaronsonAmbainis_Row_DisjointBlocks
import Definitions.Def_AaronsonAmbainis_Pack_Main
import Definitions.Def_AaronsonAmbainis_Dual_Main
import Definitions.Def_AaronsonAmbainis_MainTheorem
import Definitions.Def_AaronsonAmbainis_Chain
set_option autoImplicit true
open AaronsonAmbainis

theorem AaronsonAmbainis.sensitivityBound : SensitivityBound := by sorry
