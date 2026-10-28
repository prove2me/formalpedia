-- Prove2me | Theorems.Thm_FeynmanKac_discount_zero_potential
-- name    : FeynmanKac.discount_zero_potential
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:12:13.592085+00:00
-- url     : https://prove2.me/theorems/2f3f7d46-3731-4fff-9232-0f3b8ff9b47a
-- title:
--   Zero potential produces unit exponential discount
-- statement:
--   For identically zero discounting or killing potential, the exponent of the discount factor is the integral of zero on any pair of endpoints. That integral vanishes, so the exponential discount equals one. The expanded formula has no dependency on separately published definition modules, permitting this independent mathematical leaf to compile.
-- source:
--   Wikipedia Feynman–Kac formula https://en.wikipedia.org/wiki/Feynman%E2%80%93Kac_formula

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

theorem FeynmanKac.discount_zero_potential (t s : ℝ) :
    Real.exp (-(∫ r in t..s, (0 : ℝ))) = 1 := by sorry
