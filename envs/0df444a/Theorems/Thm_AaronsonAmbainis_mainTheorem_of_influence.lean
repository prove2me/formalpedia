-- Prove2me | Theorems.Thm_AaronsonAmbainis_mainTheorem_of_influence
-- name    : AaronsonAmbainis.mainTheorem_of_influence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:08:24.70483+00:00
-- url     : https://prove2.me/theorems/f05730fe-784e-4641-b0ea-55ddf191ff1a
-- title:
--   Aaronson Ambainis: main Theorem of influence
-- statement:
--   The main theorem (Theorem 1.1 of the paper) from the bound for the influences (Theorem 8.3),
--   the sensitivity bound (Corollary 6.10) and the row bound (Theorem 6.8).
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/MainTheorem.lean#L34-L40
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/MainTheorem.lean#L34-L40

import Definitions.Def_AaronsonAmbainis_Average_Influence
import Definitions.Def_AaronsonAmbainis_Row_Degree
import Definitions.Def_AaronsonAmbainis_MainTheorem
set_option autoImplicit true
open AaronsonAmbainis
open Finset

theorem AaronsonAmbainis.mainTheorem_of_influence :
    InfluenceBound → SensitivityBound → RowBoundPM → MainTheorem := by sorry
