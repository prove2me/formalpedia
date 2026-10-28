-- Prove2me | Theorems.Thm_FeynmanKac_discount_at_start
-- name    : FeynmanKac.discount_at_start
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T19:29:03.019848+00:00
-- url     : https://prove2.me/theorems/94b5b5af-b7c9-4075-b5d9-724e7a66b410
-- title:
--   Pathwise discount equals one at its starting time
-- statement:
--   Pathwise exponential discount over a zero-length time interval equals one.
-- source:
--   https://en.wikipedia.org/wiki/Feynman%E2%80%93Kac_formula

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

theorem FeynmanKac.discount_at_start
    {Ω : Type*} (X : ℝ → Ω → ℝ) (V : ℝ → ℝ → ℝ)
    (t : ℝ) (ω : Ω) :
    Real.exp (-(∫ r in t..t, V (X r ω) r)) = 1 := by sorry
