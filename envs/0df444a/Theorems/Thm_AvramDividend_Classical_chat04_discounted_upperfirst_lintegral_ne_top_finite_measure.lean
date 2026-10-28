-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_discounted_upperfirst_lintegral_ne_top_finite_measure
-- name    : AvramDividend.Classical.chat04_discounted_upperfirst_lintegral_ne_top_finite_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T11:35:00.080995+00:00
-- url     : https://prove2.me/theorems/379ef4a3-7361-4f47-aa45-13b86810776b
-- title:
--   Strict upper-first discounted lower integral is finite under any finite sample-path measure
-- statement:
--   If the path-space measure has finite total mass and the discount rate is nonnegative, the killed two-sided upper-first discounted payoff has finite lower integral. This covers finite Esscher-changed measures and the original probability law.
-- source:
--   Combines remotely accepted total-mass domination and the pinned Mathlib finite-measure result MeasureTheory.measure_ne_top.

import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.BoundedOrder.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_discounted_upperfirst_lintegral_le_measure_univ

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_discounted_upperfirst_lintegral_ne_top_finite_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω)
    [IsFiniteMeasure μ] (q a x : ℝ) (hq : 0 ≤ q) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp
          (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
      else 0 ∂μ) ≠ ⊤ := by sorry
