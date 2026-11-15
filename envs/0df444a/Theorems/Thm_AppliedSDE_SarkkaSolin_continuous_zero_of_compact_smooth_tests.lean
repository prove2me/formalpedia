-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_continuous_zero_of_compact_smooth_tests
-- name    : AppliedSDE.SarkkaSolin.continuous_zero_of_compact_smooth_tests
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T11:13:59.457863+00:00
-- url     : https://prove2.me/theorems/f5f4e22f-e67d-42bb-a84c-20c9d70c5190
-- title:
--   Fundamental lemma: continuous residual annihilating compact C2 tests vanishes pointwise
-- statement:
--   A continuous real function g that integrates to zero against every C2 compactly supported real test function is identically zero. The fundamental lemma of the calculus of variations provides the distributional-to-pointwise step needed for time-dependent Kolmogorov forward/Fokker Planck PDEs.
-- source:
--   Sarkka and Solin (2019), forward Kolmogorov Fokker Planck equation; supporting theorem e3ca70d5-5894-4f8f-a06e-e1797eeadb55. Also closely related to proven StationaryAction fundamental lemma 393d8bc6-cfd5-4f75-af71-459907e0fdcd.

import Mathlib
open MeasureTheory
open scoped Topology

theorem AppliedSDE.SarkkaSolin.continuous_zero_of_compact_smooth_tests
    (g : ℝ -> ℝ) (hg : Continuous g)
    (htest : ∀ (φ : ℝ -> ℝ),
      ContDiff ℝ 2 φ -> HasCompactSupport φ ->
        (∫ x : ℝ, φ x * g x) = 0) :
    ∀ x : ℝ, g x = 0 := by
  sorry
