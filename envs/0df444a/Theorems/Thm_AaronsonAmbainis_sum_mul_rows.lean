-- Prove2me | Theorems.Thm_AaronsonAmbainis_sum_mul_rows
-- name    : AaronsonAmbainis.sum_mul_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:18:30.064226+00:00
-- url     : https://prove2.me/theorems/a97db32e-c461-4542-826a-1bb65c314ea8
-- title:
--   Aaronson Ambainis: sum mul rows
-- statement:
--   Expanding a weighted sum of products of two combinations of rows.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/CauchySchwarz.lean#L32-L52
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/CauchySchwarz.lean#L32-L52

import Mathlib
import Definitions.Def_AaronsonAmbainis_TwoSided_CauchySchwarz
set_option autoImplicit true
open AaronsonAmbainis
open Finset

theorem AaronsonAmbainis.sum_mul_rows {α β ι : Type*} [Fintype ι] (O : Finset α) (N : Finset β)
    (w : ι → ℝ) (u : α → ℝ) (v : β → ℝ) (f : α → ι → ℝ) (h : β → ι → ℝ) :
    ∑ j, w j * (∑ x ∈ O, u x * f x j) * (∑ y ∈ N, v y * h y j)
      = ∑ x ∈ O, ∑ y ∈ N, (u x * v y) * ∑ j, w j * f x j * h y j := by sorry
