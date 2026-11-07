-- Prove2me | Theorems.Thm_AaronsonAmbainis_le_of_sq_le_mul
-- name    : AaronsonAmbainis.le_of_sq_le_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:18:21.364323+00:00
-- url     : https://prove2.me/theorems/9519a45f-b0ba-4769-8a63-1a51a57b60f1
-- title:
--   Aaronson Ambainis: le of sq le mul
-- statement:
--   `P ^ 2 ≤ C * P` and `0 ≤ C` give `P ≤ C`.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/CauchySchwarz.lean#L130-L134
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/TwoSided/CauchySchwarz.lean#L130-L134

import Mathlib
import Definitions.Def_AaronsonAmbainis_TwoSided_CauchySchwarz
set_option autoImplicit true
open AaronsonAmbainis
open Finset

theorem AaronsonAmbainis.le_of_sq_le_mul {P C : ℝ} (hC : 0 ≤ C) (h : P ^ 2 ≤ C * P) : P ≤ C := by sorry
