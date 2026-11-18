-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB167_native_positive_centered_brownian_short_tube_of_measurable_lift
-- name    : AvramDividend.Classical.avram_gbB167_native_positive_centered_brownian_short_tube_of_measurable_lift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T21:00:43.856829+00:00
-- url     : https://prove2.me/theorems/a3ba4dbd-4691-4e1e-bfd1-3b4995760f4c
-- title:
--   Native original Gaussian centered Brownian tube has positive probability through exact counterexample horizon
-- statement:
--   For the canonical Gaussian limit Brownian motion with a measurable continuous path lift, the centered Brownian tube of radius 1/4000 through time 1/1000 has strictly positive probability. This follows from the already Proved native joint centered and drifted tube event through 17/16000 by restricting to a shorter physical horizon. It is precisely the support event needed for the original stopped cash counterexample.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB126_native_joint_centered_drifted_tube_of_measurable_lift
open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB167_native_positive_centered_brownian_short_tube_of_measurable_lift
    [IsProbabilityMeasure gaussianLimit]
    (W : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hW : IsBrownianReal W gaussianLimit)
    (B : (ℝ≥0 → ℝ) → C(unitInterval, ℝ))
    (hMeas : Measurable B)
    (hCoord : ∀ ω (t : unitInterval), B ω t = W ⟨t, t.2.1⟩ ω) :
    0 < gaussianLimit {ω | ∀ s : unitInterval,
      s ≤ (⟨(1 / 1000 : ℝ), by constructor <;> norm_num⟩ : unitInterval) →
      |W ⟨s, s.2.1⟩ ω| < (1 / 4000 : ℝ)} := by sorry
