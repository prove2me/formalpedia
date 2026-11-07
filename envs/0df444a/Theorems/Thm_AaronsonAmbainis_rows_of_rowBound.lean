-- Prove2me | Theorems.Thm_AaronsonAmbainis_rows_of_rowBound
-- name    : AaronsonAmbainis.rows_of_rowBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:02:00.868127+00:00
-- url     : https://prove2.me/theorems/d4e20388-31a5-4341-ac2d-9064bc3d352a
-- title:
--   Aaronson Ambainis: rows of row Bound
-- statement:
--   The row bound of Agarwal and Ben-David (the hypothesis `RowBound`) for a function `f` with
--   values in `[-1,1]`: applied to `(1 + f)/2`, with the weights doubled, it gives rows of `f` of
--   cost at most `π² d² / 2`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/MainTheorem.lean#L56-L83
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/MainTheorem.lean#L56-L83

import Definitions.Def_AaronsonAmbainis_Average_Influence
import Definitions.Def_AaronsonAmbainis_Row_Degree
import Definitions.Def_AaronsonAmbainis_MainTheorem
set_option autoImplicit true
open AaronsonAmbainis
open Finset

theorem AaronsonAmbainis.rows_of_rowBound (hRB : RowBound) {ι : Type} [Fintype ι] [DecidableEq ι] (d : ℕ)
    (f : Cube ι → ℝ) (hf : ∀ x, |f x| ≤ 1) (hdeg : HasDegreeLE f d) :
    ∃ a : Cube ι → ι → ℝ, (∀ x i, 0 ≤ a x i) ∧
      (∀ x, ∑ i, a x i ≤ Real.pi ^ 2 * (d : ℝ) ^ 2 / 2) ∧
      ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, a x i := by sorry
