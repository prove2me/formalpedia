-- Prove2me | Theorems.Thm_AaronsonAmbainis_meanIncrementDegree_of_meanIncrement
-- name    : AaronsonAmbainis.meanIncrementDegree_of_meanIncrement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:09:15.591531+00:00
-- url     : https://prove2.me/theorems/26e388b1-6207-48ba-940e-95ca0640064c
-- title:
--   Aaronson Ambainis: mean Increment Degree of mean Increment
-- statement:
--   The bound for the mean absolute increments of a bounded function of degree at most `d`
--   (Corollary 7.11 of the paper), from the bound for functions with rows of cost at most `K`
--   (Theorem 7.10) and the row bound (Theorem 6.8).
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/MainTheorem.lean#L45-L51
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/MainTheorem.lean#L45-L51

import Definitions.Def_AaronsonAmbainis_Average_Influence
import Definitions.Def_AaronsonAmbainis_Row_Degree
import Definitions.Def_AaronsonAmbainis_MainTheorem
set_option autoImplicit true
open AaronsonAmbainis
open Finset

theorem AaronsonAmbainis.meanIncrementDegree_of_meanIncrement :
    MeanIncrementBound → RowBoundPM → MeanIncrementDegreeBound := by sorry
