-- Prove2me | Theorems.Thm_AaronsonAmbainis_two_mul_sum_finset_sum
-- name    : AaronsonAmbainis.two_mul_sum_finset_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:30:35.70669+00:00
-- url     : https://prove2.me/theorems/ce64a964-337b-4243-ba16-23b3a4847360
-- title:
--   Aaronson Ambainis: two mul sum finset sum
-- statement:
--   Each coordinate lies in exactly half of all sets.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/AllPairs.lean#L43-L59
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/AllPairs.lean#L43-L59

import Definitions.Def_AaronsonAmbainis_TwoSided_AllPairsCore
import Definitions.Def_AaronsonAmbainis_TwoSided_AllPairs
set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.two_mul_sum_finset_sum (β : ι → ℝ) :
    2 * ∑ F : Finset ι, ∑ j ∈ F, β j = 2 ^ Fintype.card ι * ∑ j, β j := by sorry
