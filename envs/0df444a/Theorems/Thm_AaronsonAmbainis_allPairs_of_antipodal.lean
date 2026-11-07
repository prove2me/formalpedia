-- Prove2me | Theorems.Thm_AaronsonAmbainis_allPairs_of_antipodal
-- name    : AaronsonAmbainis.allPairs_of_antipodal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:33:44.043085+00:00
-- url     : https://prove2.me/theorems/10b5bdf7-5982-4434-bac9-e05b58bd6fd2
-- title:
--   Aaronson Ambainis: all Pairs of antipodal
-- statement:
--   The all-pairs inequality (the inequality of Proposition 5.2 of the paper, multiplied by `2`)
--   from the antipodal inequality (Theorem 4.3).
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/AllPairs.lean#L63-L93
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/AllPairs.lean#L63-L93

import Definitions.Def_AaronsonAmbainis_TwoSided_AllPairsCore
import Definitions.Def_AaronsonAmbainis_TwoSided_AllPairs
set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.allPairs_of_antipodal : AntipodalInequality → AllPairsInequality := by sorry
