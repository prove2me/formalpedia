-- Prove2me | Theorems.Thm_AaronsonAmbainis_Average_variance_avg
-- name    : AaronsonAmbainis.Average.variance_avg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:35:47.813204+00:00
-- url     : https://prove2.me/theorems/5c308fb6-ffdf-47d2-9e8b-f800b8fba8e0
-- title:
--   Average: variance avg
-- statement:
--   `Var f = Var (avg j f) + Inf_j f`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Average/Coordinate.lean#L72-L91
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Average/Coordinate.lean#L72-L91

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Average_Coordinate
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Average
open Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Average.variance_avg (j : ι) (f : Cube ι → ℝ) :
    variance f = variance (avg j f) + inflR f j := by sorry
