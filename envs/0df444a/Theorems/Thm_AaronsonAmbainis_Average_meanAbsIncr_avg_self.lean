-- Prove2me | Theorems.Thm_AaronsonAmbainis_Average_meanAbsIncr_avg_self
-- name    : AaronsonAmbainis.Average.meanAbsIncr_avg_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:35:46.199592+00:00
-- url     : https://prove2.me/theorems/44135541-e9cd-4b30-9dd1-3afa41ed9db3
-- title:
--   Average: mean Abs Incr avg self
-- statement:
--   `L_j (avg j f) = 0`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Average/Coordinate.lean#L149-L151
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Average/Coordinate.lean#L149-L151

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Average_Coordinate
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Average
open Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Average.meanAbsIncr_avg_self (j : ι) (f : Cube ι → ℝ) : meanAbsIncr (avg j f) j = 0 := by sorry
