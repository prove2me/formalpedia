-- Prove2me | Theorems.Thm_AaronsonAmbainis_bdry_glue_of_not_mem
-- name    : AaronsonAmbainis.bdry_glue_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:29:30.725372+00:00
-- url     : https://prove2.me/theorems/9495af6b-0ef8-494e-a222-d3f4743098c8
-- title:
--   Aaronson Ambainis: bdry glue of not mem
-- statement:
--   A coordinate that is not free has no bichromatic edge in the subcube.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/AllPairsCore.lean#L87-L95
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/AllPairsCore.lean#L87-L95

import Definitions.Def_AaronsonAmbainis_TwoSided_Glue
import Definitions.Def_AaronsonAmbainis_TwoSided_AllPairsCore
set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.bdry_glue_of_not_mem (g : Cube ι → Bool) {F : Finset ι} {j : ι} (hj : j ∉ F)
    (z : Cube ι) : bdry (fun u => g (glue F z u)) j = 0 := by sorry
