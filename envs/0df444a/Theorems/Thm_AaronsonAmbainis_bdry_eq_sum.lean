-- Prove2me | Theorems.Thm_AaronsonAmbainis_bdry_eq_sum
-- name    : AaronsonAmbainis.bdry_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:29:47.26587+00:00
-- url     : https://prove2.me/theorems/3e524dcb-3029-4942-b51b-5906433fd435
-- title:
--   Aaronson Ambainis: bdry eq sum
-- statement:
--   `bdry` as a real sum of indicators.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/AllPairsCore.lean#L81-L84
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/AllPairsCore.lean#L81-L84

import Definitions.Def_AaronsonAmbainis_TwoSided_Glue
import Definitions.Def_AaronsonAmbainis_TwoSided_AllPairsCore
set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.bdry_eq_sum (g : Cube ι → Bool) (j : ι) :
    (bdry g j : ℝ) = ∑ x, (if g x = true ∧ g (flipSet x {j}) = false then (1 : ℝ) else 0) := by sorry
