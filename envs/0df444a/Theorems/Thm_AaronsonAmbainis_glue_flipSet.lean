-- Prove2me | Theorems.Thm_AaronsonAmbainis_glue_flipSet
-- name    : AaronsonAmbainis.glue_flipSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:26:13.574237+00:00
-- url     : https://prove2.me/theorems/e9c74072-dbb3-49c0-b4b4-3f6bceeb18de
-- title:
--   Aaronson Ambainis: glue flip Set
-- statement:
--   The Aaronson Ambainis construction uses the glue flip Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Glue.lean#L27-L30
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Glue.lean#L27-L30

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_TwoSided_Glue
set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [DecidableEq ι]

theorem AaronsonAmbainis.glue_flipSet (F : Finset ι) (z u : Cube ι) (S : Finset ι) :
    glue F z (flipSet u S) = flipSet (glue F z u) (S ∩ F) := by sorry
