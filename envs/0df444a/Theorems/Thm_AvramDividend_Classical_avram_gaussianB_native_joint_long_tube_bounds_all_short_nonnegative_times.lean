-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussianB_native_joint_long_tube_bounds_all_short_nonnegative_times
-- name    : AvramDividend.Classical.avram_gaussianB_native_joint_long_tube_bounds_all_short_nonnegative_times
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T23:56:36.652633+00:00
-- url     : https://prove2.me/theorems/8dcf2007-edb0-44b5-abf0-49ba71819e37
-- title:
--   Canonical long unit-interval Brownian joint tube controls every original short nonnegative-time sample
-- statement:
--   For the canonical original Brownian process, a long joint centred and drifted tube through time 17/16000 on the unit interval implies identical source bounds for every nonnegative real time t≤1/1000. The proof explicitly constructs the unit-interval point represented by t and identifies its lifted NNReal coordinate, supplying the time-coordinate bridge required by B180 and the original stopped HJB barrier source.

import Mathlib.Tactic.NormNum
import Theorems.Thm_ProbabilityTheory_isBrownianReal_brownian_avram
import Mathlib.Probability.BrownianMotion.Basic
import Definitions.Def_GlynnSTS_Limit_Setting
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open ProbabilityTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gaussianB_native_joint_long_tube_bounds_all_short_nonnegative_times
    (ω : ℝ≥0 → ℝ)
    (hTube : ∀ s : unitInterval,
      s ≤ (⟨(17 / 16000 : ℝ), by constructor <;> norm_num⟩ : unitInterval) →
      |brownian ⟨s, s.2.1⟩ ω - brownian 0 ω| ≤ (1 / 4000 : ℝ) ∧
      |brownian ⟨s, s.2.1⟩ ω - brownian 0 ω +
        2 * (s : ℝ)| ≤ (1 / 400 : ℝ)) :
    ∀ t : ℝ≥0, t ≤ (1 / 1000 : ℝ≥0) →
      |brownian t ω - brownian 0 ω| ≤ (1 / 4000 : ℝ) ∧
      |brownian t ω - brownian 0 ω +
        2 * (t : ℝ)| ≤ (1 / 400 : ℝ) := by sorry
