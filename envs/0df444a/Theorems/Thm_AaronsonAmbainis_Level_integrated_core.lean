-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_integrated_core
-- name    : AaronsonAmbainis.Level.integrated_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:35:50.138594+00:00
-- url     : https://prove2.me/theorems/86331dcd-401f-43d7-be04-3cde91697b2f
-- title:
--   Level: integrated core
-- statement:
--   The integrated all-pairs inequality, in the form that comes out of the integration over the
--   level.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Integrated.lean#L33-L85
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/Integrated.lean#L33-L85

import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Level_Integral
import Definitions.Def_AaronsonAmbainis_Level_AllPairs
import Definitions.Def_AaronsonAmbainis_Level_Integrated
set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Level
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Level.integrated_core (hAllPairs : AllPairsInequality) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ)
    (ha : ∀ x j, 0 ≤ a x j) (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j)
    (w : ι → ℝ) (hw : ∀ j, 0 < w j) :
    2 * ∑ x, ∑ y, max (f x - f y) 0 ^ 3 / 6 * (∑ j ∈ diffSet x y, w j * a x j * a y j)⁻¹
      ≤ 2 ^ Fintype.card ι * ∑ j, (∑ x, max (f x - f (flipSet x {j})) 0) / w j := by sorry
