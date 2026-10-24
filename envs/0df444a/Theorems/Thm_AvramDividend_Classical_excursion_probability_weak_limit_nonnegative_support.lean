-- Prove2me | Theorems.Thm_AvramDividend_Classical_excursion_probability_weak_limit_nonnegative_support
-- name    : AvramDividend.Classical.excursion_probability_weak_limit_nonnegative_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:18:00.549971+00:00
-- url     : https://prove2.me/theorems/0515da7e-aa6f-4d74-8184-cd4b16051cb1
-- title:
--   Nonnegative support survives weak probability-measure limits
-- statement:
--   A weak limit of probability measures supported on the nonnegative half-line retains support there; use the open-set Portmanteau inequality.
-- source:
--   Pinned Mathlib Portmanteau; single targeted import after multi-import authoring compilation failures.

import Mathlib.MeasureTheory.Measure.Portmanteau

open MeasureTheory Filter Set Topology

theorem AvramDividend.Classical.excursion_probability_weak_limit_nonnegative_support
    (ν : ℕ → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (hν : Tendsto ν atTop (𝓝 μ))
    (hsupport : ∀ n : ℕ, (ν n : Measure ℝ) (Iio (0 : ℝ)) = 0) :
    (μ : Measure ℝ) (Iio (0 : ℝ)) = 0 := by sorry
