-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_firstRecord_one_step_scale_regeneration_upper
-- name    : AvramDividend.Classical.killed_firstRecord_one_step_scale_regeneration_upper
-- status  : Open
-- author  : @WillR
-- created : 2026-10-25T22:23:24.574537+00:00
-- url     : https://prove2.me/theorems/9c0db52e-4ddb-41ca-b8ab-d512f05e5a3b
-- title:
--   Expected killed upward-record weight satisfies the q-scale one-step upper recurrence
-- statement:
--   For a standing spectrally negative Lévy process, the expectation of the surviving discounted (n+1)-st strict record at mesh epsilon is bounded by W(a)/W(a+epsilon) times the expected surviving discounted n-th record. Prove using the genuine strong Markov property at the nth record, the no-positive-jumps record identity, and the q-scale two-sided-exit formula. This is the exact outstanding stochastic premise of the Proved barrierSupValue_stopped_renewal_upper_of_eventual_expected_step reduction.
-- source:
--   The actual killed q-scale one-step renewal inequality underlying the upper half of Proposition 1. Root-connected through the already Proved eventual expected-step reduction; no conditional Markov identity assumed.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.killed_firstRecord_one_step_scale_regeneration_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a ε : ℝ) (ha : 0 < a)
    (hε : 0 < ε) (hWright : 0 < W (a + ε)) (hWa : 0 ≤ W a)
    (hWinc : W a < W (a + ε)) (n : ℕ) :
    (∫⁻ ω, if twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal
          (ε * Real.exp (-(q * (twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω).toReal)))
      else 0 ∂P) ≤
    ENNReal.ofReal (W a / W (a + ε)) *
    (∫⁻ ω, if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal
          (ε * Real.exp (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
      else 0 ∂P) := by sorry
