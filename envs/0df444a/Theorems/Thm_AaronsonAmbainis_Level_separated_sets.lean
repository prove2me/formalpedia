-- Prove2me | Theorems.Thm_AaronsonAmbainis_Level_separated_sets
-- name    : AaronsonAmbainis.Level.separated_sets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:39:28.610615+00:00
-- url     : https://prove2.me/theorems/3b430a72-2ce8-4ed5-b388-bfe27132cd53
-- title:
--   Level: separated sets
-- statement:
--   Two separated sets (Corollary 7.7 of the paper). If `f` has rows of cost at most `K`
--   everywhere, `M ≥ 0` bounds all `L_j = meanAbsIncr f j`, and `f ≥ s + θ` on `A`, `f ≤ s` on `B`
--   with `θ ≥ 0`, then `2 θ^3 μ(A) μ(B) ≤ 3 K² M` (`μ` the uniform probability on the cube).
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/ThirdMoment.lean#L259-L296
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Level/ThirdMoment.lean#L259-L296

import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Level_AllPairs
import Definitions.Def_AaronsonAmbainis_TwoSided_CauchySchwarz
import Definitions.Def_AaronsonAmbainis_Level_ThirdMoment
set_option autoImplicit true
open AaronsonAmbainis
open Finset
open AaronsonAmbainis.Level
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Level.separated_sets (hTM : ThirdMomentInequality) (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ)
    (ha : ∀ x j, 0 ≤ a x j) {K : ℝ} (hsum : ∀ x, ∑ j, a x j ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ j ∈ diffSet x y, a x j)
    {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ j, meanAbsIncr f j ≤ M)
    (A B : Finset (Cube ι)) (s θ : ℝ) (hθ : 0 ≤ θ)
    (hA : ∀ x ∈ A, s + θ ≤ f x) (hB : ∀ y ∈ B, f y ≤ s) :
    2 * θ ^ 3 * ((A.card : ℝ) / 2 ^ Fintype.card ι) * ((B.card : ℝ) / 2 ^ Fintype.card ι)
      ≤ 3 * K ^ 2 * M := by sorry
