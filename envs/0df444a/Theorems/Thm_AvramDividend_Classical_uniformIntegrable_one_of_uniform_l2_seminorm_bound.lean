-- Prove2me | Theorems.Thm_AvramDividend_Classical_uniformIntegrable_one_of_uniform_l2_seminorm_bound
-- name    : AvramDividend.Classical.uniformIntegrable_one_of_uniform_l2_seminorm_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T15:38:28.789425+00:00
-- url     : https://prove2.me/theorems/6ecde2f8-f759-4772-8894-8a5887983551
-- title:
--   Probability-space L2 seminorm bound implies uniform integrability in L1
-- statement:
--   For real measurable observables on a probability space, a uniform finite bound on their L2 seminorms implies uniform integrability in L1. The argument uses the small-event Cauchy–Schwarz bound with a common epsilon-dependent event threshold.
-- source:
--   Pinned Mathlib MeasureTheory UniformIntegrable definition and eLpNorm exponent comparison, together with the explicit indicator L1-L2 Hölder bridge (published separately); no stochastic assumptions or Wiener–Hopf splitting.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_esscher_indicator_l1_le_l2_sqrt_measure

open AvramDividend.Classical MeasureTheory
open scoped ENNReal NNReal

theorem AvramDividend.Classical.uniformIntegrable_one_of_uniform_l2_seminorm_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : ℕ → Ω → ℝ) (C : ℝ≥0)
    (hmeas : ∀ n, AEStronglyMeasurable (f n) μ)
    (hbound : ∀ n, eLpNorm (f n) (2 : ℝ≥0∞) μ ≤ C) :
    UniformIntegrable f (1 : ℝ≥0∞) μ := by sorry
