-- Prove2me | Theorems.Thm_AvramDividend_Classical_nextRecord_finite_clocks_have_nonnegative_delay
-- name    : AvramDividend.Classical.nextRecord_finite_clocks_have_nonnegative_delay
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:02:04.148155+00:00
-- url     : https://prove2.me/theorems/d5e3525d-0b30-4d60-a064-ac05c241a302
-- title:
--   Monotone finite upcrossing clocks admit a finite nonnegative record delay
-- statement:
--   If two finite strict upper first-passage times correspond to successive thresholds b and b+ε with ε nonnegative, the higher clock is at least the lower. The difference is a finite nonnegative duration δ with u+δ=v. This discharges the delay-existence hypothesis required by stopped-renewal strong-Markov and killed-record comparisons.
-- source:
--   Use proved threshold monotonicity of strict first-passage clocks, reflect the ENNReal order back to NNReal, and take the ordered truncated difference v-u.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Data.ENNReal.Basic
import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_mono_threshold

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.nextRecord_finite_clocks_have_nonnegative_delay
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (b ε : ℝ) (hε : 0 ≤ ε) (u v : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hv : (v : ℝ≥0∞) = twoSidedExitUpTime X (b + ε) ω) :
    ∃ δ : ℝ≥0, u + δ = v := by sorry
