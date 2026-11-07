-- Prove2me | Theorems.Thm_AaronsonAmbainis_Row_sum_abs_le_of_abs_sum_le
-- name    : AaronsonAmbainis.Row.sum_abs_le_of_abs_sum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:58:01.118775+00:00
-- url     : https://prove2.me/theorems/08ff4820-4ac6-43ba-9a6e-0091fedc954e
-- title:
--   Row: sum abs le of abs sum le
-- statement:
--   If every partial sum of `d` is bounded by `K` in absolute value, then `∑ |d| ≤ 2 K`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Sensitivity.lean#L18-L30
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Row/Sensitivity.lean#L18-L30

import Definitions.Def_AaronsonAmbainis_Row_Extension
import Definitions.Def_AaronsonAmbainis_Row_Sensitivity
set_option autoImplicit true
open AaronsonAmbainis
open AaronsonAmbainis.Row
open Finset Polynomial

theorem AaronsonAmbainis.Row.sum_abs_le_of_abs_sum_le {β : Type*} [Fintype β] (d : β → ℝ) (K : ℝ)
    (h : ∀ R : Finset β, |∑ b ∈ R, d b| ≤ K) : ∑ b, |d b| ≤ 2 * K := by sorry
