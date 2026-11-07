-- Prove2me | Theorems.Thm_AaronsonAmbainis_allPairs_core
-- name    : AaronsonAmbainis.allPairs_core
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:29:47.989355+00:00
-- url     : https://prove2.me/theorems/3a5db352-639a-41d1-ab9f-71ff876bb6a7
-- title:
--   Aaronson Ambainis: all Pairs core
-- statement:
--   The inequality for one set `F` of free coordinates (Step 1 of the proof of Proposition 5.2
--   of the paper), from the antipodal inequality.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/AllPairsCore.lean#L114-L145
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/AllPairsCore.lean#L114-L145

import Definitions.Def_AaronsonAmbainis_TwoSided_Glue
import Definitions.Def_AaronsonAmbainis_TwoSided_AllPairsCore
set_option autoImplicit true
open AaronsonAmbainis
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.allPairs_core (hAntipodal : AntipodalInequality) {ι : Type} [Fintype ι] [DecidableEq ι]
    (g : Cube ι → Bool) (w : ι → ℝ) (hw : ∀ j, 0 < w j)
    (lam : Cube ι → ι → ℝ) (hlam : ∀ x, IsRow g x (lam x)) (F : Finset ι) :
    ∑ x, allPairsTerm g w lam F x ≤ ∑ j ∈ F, (bdry g j : ℝ) / w j := by sorry
