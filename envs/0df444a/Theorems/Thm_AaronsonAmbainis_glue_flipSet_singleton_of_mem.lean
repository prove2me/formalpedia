-- Prove2me | Theorems.Thm_AaronsonAmbainis_glue_flipSet_singleton_of_mem
-- name    : AaronsonAmbainis.glue_flipSet_singleton_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:26:51.806516+00:00
-- url     : https://prove2.me/theorems/902d8229-3a31-4139-91f5-bb06bf207d79
-- title:
--   Aaronson Ambainis: glue flip Set singleton of mem
-- statement:
--   The Aaronson Ambainis construction uses the glue flip Set singleton of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Glue.lean#L37-L39
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Glue.lean#L37-L39

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_TwoSided_Glue
set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [DecidableEq ι]

theorem AaronsonAmbainis.glue_flipSet_singleton_of_mem {F : Finset ι} {j : ι} (hj : j ∈ F) (z u : Cube ι) :
    glue F z (flipSet u {j}) = flipSet (glue F z u) {j} := by sorry
