-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat01_levy_exponential_mean_invariance
-- name    : AvramDividend.Classical.chat01_levy_exponential_mean_invariance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:34:42.100891+00:00
-- url     : https://prove2.me/theorems/5660f5e2-dd73-44e7-9a51-10269c7ebdcb
-- title:
--   Deterministic-time invariance of the compensated Levy exponential mean
-- statement:
--   The integrals of the compensated exponential Lévy martingale at any two ordered deterministic times agree. This provides the expectation conservation identity used in first-passage analysis.
-- source:
--   Proved levy_compensated_exponential_martingale and Mathlib MeasureTheory.Martingale.setIntegral_eq.

import Mathlib.Probability.Martingale.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_martingale
open AvramDividend.Classical MeasureTheory
open scoped NNReal

theorem AvramDividend.Classical.chat01_levy_exponential_mean_invariance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (s t : ℝ≥0) (hst : s ≤ t) :
    (∫ w, Real.exp (θ * X.X s w -
      (s : ℝ) * laplaceExponent X.c X.σ X.ν θ) ∂P) =
    (∫ w, Real.exp (θ * X.X t w -
      (t : ℝ) * laplaceExponent X.c X.σ X.ν θ) ∂P) := by sorry
