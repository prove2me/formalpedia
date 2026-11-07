-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_pairSum_pos
-- name    : AaronsonAmbainis.Level.pairSum_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:36:18.865272+00:00
-- url     : https://prove2.me/theorems/01bb4226-261b-4eab-b6c9-67fbd5f35229
-- title:
--   Level: pair Sum pos
-- statement:
--   Rows at two points with different values overlap on the difference set: `s_xy > 0`
--   (Lemma 7.1 (ii) of the paper).
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/AllPairs.lean#L52-L69
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/AllPairs.lean#L52-L69

import Definitions.Def_AaronsonAmbainis_Level_Rows
import Definitions.Def_AaronsonAmbainis_TwoSided_Overlap
import Definitions.Def_AaronsonAmbainis_Level_AllPairs
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Level
open Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Level.pairSum_pos {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ} (ha : ∀ x j, 0 ≤ a x j)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j) {w : ι → ℝ} (hw : ∀ j, 0 < w j)
    {x y : Cube ι} (hxy : f y < f x) :
    0 < ∑ j ∈ diffSet x y, w j * a x j * a y j := by sorry
