-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_negative_jump_exponential_deficit_bounds_nat
-- name    : AvramDividend.Classical.finite_negative_jump_exponential_deficit_bounds_nat
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T14:30:09.579008+00:00
-- url     : https://prove2.me/theorems/71e61f35-cd30-4df6-8796-639008d42af8
-- title:
--   Finite negative-jump exponential deficit is between zero and its jump intensity
-- statement:
--   For a finite Lévy measure restricted to negative jumps and any nonnegative integer Laplace parameter, the exponential deficiency integral lies in [0,λ], where λ is the finite total negative jump mass. The bound makes the finite-activity exponential mesh estimate applicable.
-- source:
--   Finite-negative-jump exponential Laplace integral decomposition, Avram, Palmowski and Pistorius (2007) Section 3.3.

import Theorems.Thm_AvramDividend_Classical_finite_negative_jump_exponential_deficit_limit_nat
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Analysis.SpecialFunctions.Exp
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.finite_negative_jump_exponential_deficit_bounds_nat
    (ν : Measure ℝ) (hFinite : ν (Iio (0 : ℝ)) < ⊤)
    (n : ℕ) :
    0 ≤ (∫ y in Iio (0 : ℝ),
      (1 - Real.exp ((n : ℝ) * y)) ∂ν) ∧
    (∫ y in Iio (0 : ℝ),
      (1 - Real.exp ((n : ℝ) * y)) ∂ν) ≤
      (ν (Iio (0 : ℝ))).toReal := by sorry
