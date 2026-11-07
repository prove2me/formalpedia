-- Prove2me | Theorems.Thm_AaronsonAmbainis_Row_abs_multilinear_le_one
-- name    : AaronsonAmbainis.Row.abs_multilinear_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:57:43.253904+00:00
-- url     : https://prove2.me/theorems/04882201-a6ba-4ad0-8eb6-d140e4c3604c
-- title:
--   Row: abs multilinear le one
-- statement:
--   Bounded multilinear extension (Lemma 6.2 of the paper).
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Extension.lean#L52-L76
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Extension.lean#L52-L76

import Definitions.Def_AaronsonAmbainis_Row_Chi
import Definitions.Def_AaronsonAmbainis_Row_Extension
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem AaronsonAmbainis.Row.abs_multilinear_le_one (a : Finset ι → ℝ)
    (h : ∀ z : Cube ι, |∑ T, a T * chi T z| ≤ 1) (u : ι → ℝ) (hu : ∀ i, |u i| ≤ 1) :
    |∑ T, a T * ∏ i ∈ T, u i| ≤ 1 := by sorry
