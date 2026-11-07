-- Prove2me | Theorems.Thm_AaronsonAmbainis_wingSet_lower
-- name    : AaronsonAmbainis.wingSet_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:25:56.626047+00:00
-- url     : https://prove2.me/theorems/b3dbb303-944a-476f-beb4-20cd7f0ce3ca
-- title:
--   Aaronson Ambainis: wing Set lower
-- statement:
--   The Aaronson Ambainis construction uses the wing Set lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Antipodal.lean#L98-L112
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/Antipodal.lean#L98-L112

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_TwoSided_Antipodal
set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.wingSet_lower {g : Cube ι → Bool} {u' : Cube ι} {x y w : ι → ℝ}
    (hw : ∀ j, 0 < w j) (hx : ∀ j, 0 ≤ x j) (hy : IsRow g u' y) (hu' : g u' = false)
    (G : Finset ι) (hG : Disjoint G (wingSet w x y)) (hgG : g (flipSet u' G) = true) :
    (∑ j, w j * x j * y j)⁻¹ ≤ ∑ j ∈ G, (w j)⁻¹ := by sorry
