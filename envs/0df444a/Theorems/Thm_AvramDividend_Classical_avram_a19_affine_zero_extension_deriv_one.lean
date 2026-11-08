-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_affine_zero_extension_deriv_one
-- name    : AvramDividend.Classical.avram_a19_affine_zero_extension_deriv_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T16:20:36.351361+00:00
-- url     : https://prove2.me/theorems/79112e24-82a2-4586-8366-79c8a4a62c17
-- title:
--   Derivative-one interface for the singular A19 affine zero extension
-- statement:
--   At every strictly positive surplus, the derivative of the nonnegative affine value candidate extended by zero to negative surplus equals one.
-- source:
--   Explicit regularity interface for the singular-jump countermodel of the original A19 generator cell, using pinned Mathlib local equality and derivative transport.

import Mathlib
open Set Filter

theorem AvramDividend.Classical.avram_a19_affine_zero_extension_deriv_one
    (x : ℝ) (hx : 0 < x) :
    deriv (fun y : ℝ => if y < 0 then (0 : ℝ) else 1 + y) x = 1 := by sorry
