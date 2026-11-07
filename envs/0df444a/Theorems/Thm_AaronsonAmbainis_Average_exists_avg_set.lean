-- Prove2me | Theorems.Thm_AaronsonAmbainis_Average_exists_avg_set
-- name    : AaronsonAmbainis.Average.exists_avg_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:37:52.878488+00:00
-- url     : https://prove2.me/theorems/666e84c8-3905-4840-997f-2c2fba809723
-- title:
--   Average: exists avg set
-- statement:
--   Averaging over the coordinates of a set `R` (Lemma 8.2 of the paper): a function `g` with
--   rows of the same cost, with `Var f ≤ Var g + ∑_{j ∈ R} Inf_j f`, with influences and mean
--   absolute increments not larger than those of `f`, and with `L_j g = 0` for `j ∈ R`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Average/Iterate.lean#L30-L62
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Average/Iterate.lean#L30-L62

import Definitions.Def_AaronsonAmbainis_Average_Coordinate
import Definitions.Def_AaronsonAmbainis_Level_Basic
import Definitions.Def_AaronsonAmbainis_Average_Iterate
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Average
open Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Average.exists_avg_set (f : Cube ι → ℝ) (a : Cube ι → ι → ℝ) {K : ℝ} (ha : ∀ x i, 0 ≤ a x i)
    (hsum : ∀ x, ∑ i, a x i ≤ K) (hrow : ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, a x i)
    (R : Finset ι) :
    ∃ (g : Cube ι → ℝ) (b : Cube ι → ι → ℝ),
      (∀ x i, 0 ≤ b x i) ∧ (∀ x, ∑ i, b x i ≤ K) ∧
      (∀ x y, |g x - g y| ≤ ∑ i ∈ diffSet x y, b x i) ∧
      variance f ≤ variance g + ∑ j ∈ R, inflR f j ∧
      (∀ k, inflR g k ≤ inflR f k) ∧ (∀ k, meanAbsIncr g k ≤ meanAbsIncr f k) ∧
      (∀ j ∈ R, meanAbsIncr g j = 0) := by sorry
