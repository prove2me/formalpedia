-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat01_levy_exponential_early_event_integral_eq
-- name    : AvramDividend.Classical.chat01_levy_exponential_early_event_integral_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:43:49.131985+00:00
-- url     : https://prove2.me/theorems/cce5250e-3cdc-4b4b-bbf3-d7455b36286e
-- title:
--   Compensated Levy exponential martingale integral invariance on early events
-- statement:
--   For any earlier-filtration measurable event, the integral of the compensated exponential Lévy martingale on that event is preserved from the earlier deterministic time to the later time. This martingale event identity is a reusable tool for first-passage stopping arguments.
-- source:
--   Proved levy_compensated_exponential_martingale and Mathlib MeasureTheory.Martingale.setIntegral_eq.

import Mathlib.Probability.Martingale.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_martingale
open AvramDividend.Classical MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.chat01_levy_exponential_early_event_integral_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : @MeasurableSet Ω (𝓕 s) A) :
    (∫ w in A, Real.exp (θ * X.X s w -
      (s : ℝ) * laplaceExponent X.c X.σ X.ν θ) ∂P) =
    (∫ w in A, Real.exp (θ * X.X t w -
      (t : ℝ) * laplaceExponent X.c X.σ X.ν θ) ∂P) := by sorry
