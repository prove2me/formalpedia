-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_sum_posPart_incr
-- name    : AaronsonAmbainis.Level.sum_posPart_incr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:35:55.666864+00:00
-- url     : https://prove2.me/theorems/8a7f92aa-fa66-4728-a209-142301be8b01
-- title:
--   Level: sum pos Part incr
-- statement:
--   `∑_x (f x - f (x^j))⁺ = (1/2) ∑_x |f x - f (x^j)|` (Lemma 7.3 (iii) of the paper).
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Integrated.lean#L88-L110
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Integrated.lean#L88-L110

import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Level_Integral
import Definitions.Def_AaronsonAmbainis_Level_AllPairs
import Definitions.Def_AaronsonAmbainis_Level_Integrated
set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Level
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Level.sum_posPart_incr (f : Cube ι → ℝ) (j : ι) :
    ∑ x, max (f x - f (flipSet x {j})) 0 = (∑ x, |f x - f (flipSet x {j})|) / 2 := by sorry
