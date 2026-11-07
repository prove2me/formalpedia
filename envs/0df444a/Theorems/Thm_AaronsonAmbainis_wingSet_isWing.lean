-- Prove2me | Theorems.Thm_AaronsonAmbainis_wingSet_isWing
-- name    : AaronsonAmbainis.wingSet_isWing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:26:04.472618+00:00
-- url     : https://prove2.me/theorems/ed34b827-b53d-4f31-a24c-a7b6b3f8a0bb
-- title:
--   Aaronson Ambainis: wing Set is Wing
-- statement:
--   The Aaronson Ambainis construction uses the wing Set is Wing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Antipodal.lean#L86-L96
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Antipodal.lean#L86-L96

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_TwoSided_Antipodal
set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.wingSet_isWing {g : Cube ι → Bool} {u : Cube ι} {x y w : ι → ℝ} (hu : g u = true)
    (hw : ∀ j, 0 < w j) (hx : IsRow g u x) (hy : ∀ j, 0 ≤ y j) :
    IsWing g u (wingSet w x y) := by sorry
