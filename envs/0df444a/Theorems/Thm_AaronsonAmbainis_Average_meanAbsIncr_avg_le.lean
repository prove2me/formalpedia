-- Prove2me | Theorems.Thm_AaronsonAmbainis_Average_meanAbsIncr_avg_le
-- name    : AaronsonAmbainis.Average.meanAbsIncr_avg_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:35:57.19344+00:00
-- url     : https://prove2.me/theorems/f81978bb-55d2-48ca-9e6d-6958497ccea3
-- title:
--   Average: mean Abs Incr avg le
-- statement:
--   `L_k (avg j f) ≤ L_k f` for every `k`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Average/Coordinate.lean#L119-L146
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Average/Coordinate.lean#L119-L146

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Average_Coordinate
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Average
open Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Average.meanAbsIncr_avg_le (j k : ι) (f : Cube ι → ℝ) :
    meanAbsIncr (avg j f) k ≤ meanAbsIncr f k := by sorry
