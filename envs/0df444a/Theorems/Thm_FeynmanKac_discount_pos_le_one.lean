-- Prove2me | Theorems.Thm_FeynmanKac_discount_pos_le_one
-- name    : FeynmanKac.discount_pos_le_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T19:29:03.731175+00:00
-- url     : https://prove2.me/theorems/c8d768da-a3c5-4343-a317-371a6db1ba4c
-- title:
--   Nonnegative potential bounds the exponential discount
-- statement:
--   For an integrable nonnegative potential on an ordered interval, the exponential discount is positive and at most one.
-- source:
--   https://en.wikipedia.org/wiki/Feynman%E2%80%93Kac_formula

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

theorem FeynmanKac.discount_pos_le_one
    {Ω : Type*} (X : ℝ → Ω → ℝ) (V : ℝ → ℝ → ℝ)
    (t s : ℝ) (hts : t ≤ s) (ω : Ω)
    (hV : ∀ r ∈ Set.Icc t s, 0 ≤ V (X r ω) r)
    (hInt : IntervalIntegrable (fun r => V (X r ω) r) MeasureTheory.volume t s) :
    0 < Real.exp (-(∫ r in t..s, V (X r ω) r)) ∧
    Real.exp (-(∫ r in t..s, V (X r ω) r)) ≤ 1 := by sorry
