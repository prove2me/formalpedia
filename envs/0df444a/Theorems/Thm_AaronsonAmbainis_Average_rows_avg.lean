-- Prove2me | Theorems.Thm_AaronsonAmbainis_Average_rows_avg
-- name    : AaronsonAmbainis.Average.rows_avg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:35:56.141539+00:00
-- url     : https://prove2.me/theorems/2f8387c2-259f-46b3-a8ad-da1261751a98
-- title:
--   Average: rows avg
-- statement:
--   Rows of `f` give rows of `avg j f` of the same cost.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Average/Coordinate.lean#L154-L173
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Average/Coordinate.lean#L154-L173

import Definitions.Def_AaronsonAmbainis_TwoSided_Basic
import Definitions.Def_AaronsonAmbainis_Average_Coordinate
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Average
open Finset
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Average.rows_avg (j : ι) {f : Cube ι → ℝ} {a : Cube ι → ι → ℝ} {K : ℝ}
    (ha : ∀ x i, 0 ≤ a x i) (hsum : ∀ x, ∑ i, a x i ≤ K)
    (hrow : ∀ x y, |f x - f y| ≤ ∑ i ∈ diffSet x y, a x i) :
    (∀ x i, 0 ≤ (a x i + a (flipSet x {j}) i) / 2) ∧
    (∀ x, ∑ i, (a x i + a (flipSet x {j}) i) / 2 ≤ K) ∧
    ∀ x y, |avg j f x - avg j f y| ≤ ∑ i ∈ diffSet x y, (a x i + a (flipSet x {j}) i) / 2 := by sorry
