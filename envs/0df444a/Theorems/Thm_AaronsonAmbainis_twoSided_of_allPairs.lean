-- Prove2me | Theorems.Thm_AaronsonAmbainis_twoSided_of_allPairs
-- name    : AaronsonAmbainis.twoSided_of_allPairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:36:48.076468+00:00
-- url     : https://prove2.me/theorems/79c9fa65-1139-4ab8-8756-8094e504a551
-- title:
--   Aaronson Ambainis: two Sided of all Pairs
-- statement:
--   The two-sided inequality (the inequality of Theorem 5.4 of the paper) from the all-pairs
--   inequality (Proposition 5.2).
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/RemoveWeights.lean#L32-L80
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/RemoveWeights.lean#L32-L80

import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_TwoSided_CauchySchwarz
import Definitions.Def_AaronsonAmbainis_TwoSided_RemoveWeights
set_option autoImplicit true
open AaronsonAmbainis
open Finset

theorem AaronsonAmbainis.twoSided_of_allPairs : AllPairsInequality → TwoSidedInequality := by sorry
