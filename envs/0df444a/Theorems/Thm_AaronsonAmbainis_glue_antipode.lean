-- Prove2me | Theorems.Thm_AaronsonAmbainis_glue_antipode
-- name    : AaronsonAmbainis.glue_antipode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:26:43.763903+00:00
-- url     : https://prove2.me/theorems/dbfec79d-2785-413c-a6fd-2af5a2c5c718
-- title:
--   Aaronson Ambainis: glue antipode
-- statement:
--   The Aaronson Ambainis construction uses the glue antipode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Glue.lean#L32-L35
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Glue.lean#L32-L35

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_TwoSided_Glue
set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [DecidableEq ι]

theorem AaronsonAmbainis.glue_antipode (F : Finset ι) (z u : Cube ι) :
    glue F z (antipode u) = flipSet (glue F z u) F := by sorry
