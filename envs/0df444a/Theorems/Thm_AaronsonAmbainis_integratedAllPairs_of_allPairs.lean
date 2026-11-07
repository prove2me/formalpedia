-- Prove2me | Theorems.Thm_AaronsonAmbainis_integratedAllPairs_of_allPairs
-- name    : AaronsonAmbainis.integratedAllPairs_of_allPairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:39:28.902851+00:00
-- url     : https://prove2.me/theorems/3190dfb9-49e5-4517-bd6b-fdc720557cd5
-- title:
--   Aaronson Ambainis: integrated All Pairs of all Pairs
-- statement:
--   The integrated all-pairs inequality (Proposition 7.4 of the paper) from the all-pairs
--   inequality for Boolean functions (Proposition 5.2).
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Integrated.lean#L160-L175
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Integrated.lean#L160-L175

import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Level_Integral
import Definitions.Def_AaronsonAmbainis_Level_AllPairs
import Definitions.Def_AaronsonAmbainis_Level_Integrated
set_option autoImplicit true
open AaronsonAmbainis
open Finset

theorem AaronsonAmbainis.integratedAllPairs_of_allPairs : AllPairsInequality → IntegratedAllPairsInequality := by sorry
