-- Prove2me | Theorems.Thm_AvramDividend_Classical_firstUpcrossing_weighted_survival_lintegral_sandwich
-- name    : AvramDividend.Classical.firstUpcrossing_weighted_survival_lintegral_sandwich
-- status  : Open
-- author  : @WillR
-- created : 2026-10-19T10:34:00.999976+00:00
-- url     : https://prove2.me/theorems/d1873558-56ba-4629-9f4d-1bda87c58620
-- title:
--   Weighted discounted survival integrals of raw and reflected Lévy paths satisfy two-sided bounds
-- statement:
--   For a spectrally negative Lévy path, fix a measurable-space measure P and an arbitrary extended nonnegative payoff weight w(ω), including as an application any q-discounted first-upcrossing factor. On a set G of scenarios with a finite first upward passage time u(ω) of b, the expected weight of raw survival above b−a is at most the expected weight of survival against strict reflected drawdown above a, which is at most the expected weight of raw survival above −a. This is the monotonicity of nonnegative Lebesgue integrals under the proven pathwise survival implications. It does not assert the two-sided q-scale exit distribution or stopped strong Markov renewal identity.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 1, first-passage renewal sandwich; based on accepted firstUpcrossing_drawdown_survival_sandwich (5ef377e5-c52c-4aad-ba42-49b0b4c7244d), which must be Proved before the new proof may be remotely accepted.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_drawdown_survival_sandwich

open Classical MeasureTheory Set
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.firstUpcrossing_weighted_survival_lintegral_sandwich
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b : ℝ) (u : Ω → ℝ≥0) (G : Set Ω)
    (hu : ∀ ω ∈ G, ((u ω : ℝ≥0) : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : b < X.X s ω), (s : ℝ≥0∞)))
    (w : Ω → ℝ≥0∞) :
    (∫⁻ ω, if ω ∈ G ∧
          (∀ t : ℝ≥0, t < u ω → b - a ≤ X.X t ω)
        then w ω else 0 ∂P) ≤
    (∫⁻ ω, if ω ∈ G ∧
          (∀ t : ℝ≥0, t < u ω →
            runningSup X t ω - X.X t ω ≤ a)
        then w ω else 0 ∂P) ∧
    (∫⁻ ω, if ω ∈ G ∧
          (∀ t : ℝ≥0, t < u ω →
            runningSup X t ω - X.X t ω ≤ a)
        then w ω else 0 ∂P) ≤
    (∫⁻ ω, if ω ∈ G ∧
          (∀ t : ℝ≥0, t < u ω → -a ≤ X.X t ω)
        then w ω else 0 ∂P) := by sorry
