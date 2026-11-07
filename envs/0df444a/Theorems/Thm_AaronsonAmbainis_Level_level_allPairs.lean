-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_level_allPairs
-- name    : AaronsonAmbainis.Level.level_allPairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:35:14.087126+00:00
-- url     : https://prove2.me/theorems/6b0a5b67-b604-4e43-b747-566703754978
-- title:
--   Level: level all Pairs
-- statement:
--   The all-pairs inequality at the level `t` (Lemma 7.2 of the paper, multiplied by `2`), from
--   the all-pairs inequality for Boolean functions.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/AllPairs.lean#L73-L107
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/AllPairs.lean#L73-L107

import Definitions.Def_AaronsonAmbainis_Level_Rows
import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Level_AllPairs
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Level.level_allPairs (hAllPairs : AllPairsInequality) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ)
    (ha : ∀ x j, 0 ≤ a x j) (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j)
    (w : ι → ℝ) (hw : ∀ j, 0 < w j) (t : ℝ) :
    2 * ∑ x, ∑ y, max (f x - t) 0 * max (t - f y) 0
          * (∑ j ∈ diffSet x y, w j * a x j * a y j)⁻¹
      ≤ 2 ^ Fintype.card ι * ∑ j, (bdry (lev f t) j : ℝ) / w j := by sorry
