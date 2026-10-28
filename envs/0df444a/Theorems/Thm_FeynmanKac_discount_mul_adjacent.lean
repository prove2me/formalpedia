-- Prove2me | Theorems.Thm_FeynmanKac_discount_mul_adjacent
-- name    : FeynmanKac.discount_mul_adjacent
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T19:29:04.434038+00:00
-- url     : https://prove2.me/theorems/710ac98a-3a89-4146-b20b-71aff98ec174
-- title:
--   Pathwise discount factors over adjacent intervals
-- statement:
--   For ordered adjacent intervals, cumulative pathwise exponential discount equals the product of consecutive discounts.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

theorem FeynmanKac.discount_mul_adjacent
    {Ω : Type*} (X : ℝ → Ω → ℝ) (V : ℝ → ℝ → ℝ)
    (t s r : ℝ) (hts : t ≤ s) (hsr : s ≤ r) (ω : Ω)
    (hInt : IntervalIntegrable (fun z => V (X z ω) z) MeasureTheory.volume t r) :
    Real.exp (-(∫ z in t..r, V (X z ω) z)) =
      Real.exp (-(∫ z in t..s, V (X z ω) z)) *
      Real.exp (-(∫ z in s..r, V (X z ω) z)) := by sorry
