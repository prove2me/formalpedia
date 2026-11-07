-- Prove2me | Theorems.Thm_AaronsonAmbainis_glue_flipSet_singleton_of_not_mem
-- name    : AaronsonAmbainis.glue_flipSet_singleton_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:28:33.5702+00:00
-- url     : https://prove2.me/theorems/56f2c9c3-9d8a-4989-a3e1-b83daf17f91e
-- title:
--   Aaronson Ambainis: glue flip Set singleton of not mem
-- statement:
--   The Aaronson Ambainis construction uses the glue flip Set singleton of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Glue.lean#L41-L43
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Glue.lean#L41-L43

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_TwoSided_Glue
set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [DecidableEq ι]

theorem AaronsonAmbainis.glue_flipSet_singleton_of_not_mem {F : Finset ι} {j : ι} (hj : j ∉ F) (z u : Cube ι) :
    glue F z (flipSet u {j}) = glue F z u := by sorry
