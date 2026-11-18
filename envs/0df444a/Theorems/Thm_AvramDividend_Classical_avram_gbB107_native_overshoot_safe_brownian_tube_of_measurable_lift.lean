-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB107_native_overshoot_safe_brownian_tube_of_measurable_lift
-- name    : AvramDividend.Classical.avram_gbB107_native_overshoot_safe_brownian_tube_of_measurable_lift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:14:34.522572+00:00
-- url     : https://prove2.me/theorems/845bec38-0058-41b4-a5f7-8f93e9d73e6f
-- title:
--   Native Gaussian tube positivity through the last physical-grid endpoint
-- statement:
--   The native gaussianLimit law inherits positive probability of the radius-1/400 drifted Brownian path tube through time 17/16000 when a measurable continuous-path lift is provided. The extra 1/16000 past the stopping horizon 1/1000 controls the terminal endpoint of sufficiently fine physical stopping grids.

import Mathlib
import Theorems.Thm_ProbabilityTheory_isBrownianReal_brownian_avram
import Definitions.Def_GlynnSTS_Limit_Setting
import Theorems.Thm_AvramDividend_Classical_avram_gbB106_overshoot_safe_drifted_brownian_tube
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB107_native_overshoot_safe_brownian_tube_of_measurable_lift
    [IsProbabilityMeasure gaussianLimit]
    (W : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ)
    (hW : IsBrownianReal W gaussianLimit)
    (B : (ℝ≥0 → ℝ) → C(unitInterval, ℝ))
    (hMeas : Measurable B)
    (hCoord : ∀ ω (t : unitInterval), B ω t = W ⟨t, t.2.1⟩ ω)
    (t : unitInterval) (ht : (t : ℝ) = (17 / 16000 : ℝ)) :
    0 < gaussianLimit {ω | ∀ s : unitInterval, s ≤ t →
      |W ⟨s, s.2.1⟩ ω + 2 * (s : ℝ)| < (1 / 400 : ℝ)} := by sorry
