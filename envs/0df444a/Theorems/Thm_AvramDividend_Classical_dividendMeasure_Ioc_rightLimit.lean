-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
-- name    : AvramDividend.Classical.dividendMeasure_Ioc_rightLimit
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T09:37:06.546218+00:00
-- url     : https://prove2.me/theorems/f9211de0-c48b-4907-aaf9-e9774b5831ef
-- title:
--   The dividend Stieltjes measure of a nonnegative-time half-open interval equals its rightLimit increment
-- statement:
--   For any dividend strategy D, sample path ω, and nonnegative endpoints a,b, the Stieltjes dividend measure of (a,b] is the positive part of the increment in formal right limits: dividendMeasure D ω (Ioc ↑a ↑b) = ofReal(rightLimit D b ω−rightLimit D a ω). This is the exact distribution-function identity of Mathlib StieltjesFunction.measure_Ioc after identifying the right limits of the real-time extension. It is the key to showing dividendMeasure is a measurable random measure/kernel in ω.
-- source:
--   Child dividendPath_real_rightLim_eq_rightLimit; pinned Mathlib StieltjesFunction.measure_Ioc.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendMeasure_Ioc_rightLimit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (a b : ℝ≥0) :
    dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) =
      ENNReal.ofReal (rightLimit D b ω - rightLimit D a ω) := by sorry
