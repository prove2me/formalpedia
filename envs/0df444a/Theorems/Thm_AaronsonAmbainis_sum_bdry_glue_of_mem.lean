-- Prove2me | Theorems.Thm_AaronsonAmbainis_sum_bdry_glue_of_mem
-- name    : AaronsonAmbainis.sum_bdry_glue_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:30:06.456657+00:00
-- url     : https://prove2.me/theorems/0077ebda-60a9-4d71-84ef-faa60e78246e
-- title:
--   Aaronson Ambainis: sum bdry glue of mem
-- statement:
--   A free coordinate: the bichromatic `j`-edges of all subcubes with free coordinates `F`
--   are the bichromatic `j`-edges of `g`, each `2 ^ n` times.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/AllPairsCore.lean#L99-L110
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/AllPairsCore.lean#L99-L110

import Definitions.Def_AaronsonAmbainis_TwoSided_Glue
import Definitions.Def_AaronsonAmbainis_TwoSided_AllPairsCore
set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.sum_bdry_glue_of_mem (g : Cube ι → Bool) {F : Finset ι} {j : ι} (hj : j ∈ F) :
    ∑ z, (bdry (fun u => g (glue F z u)) j : ℝ) = 2 ^ Fintype.card ι * (bdry g j : ℝ) := by sorry
