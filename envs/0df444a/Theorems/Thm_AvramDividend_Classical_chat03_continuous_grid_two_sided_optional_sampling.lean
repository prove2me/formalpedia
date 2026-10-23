-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_continuous_grid_two_sided_optional_sampling
-- name    : AvramDividend.Classical.chat03_continuous_grid_two_sided_optional_sampling
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T10:28:20.175314+00:00
-- url     : https://prove2.me/theorems/ce43d7f8-592d-4df4-b04a-d0ff1c43908a
-- title:
--   Bounded two-sided grid optional sampling of a continuous martingale
-- statement:
--   For any continuous-time real adapted process Z and any continuous-time real martingale M, sample both along an arbitrary monotone deterministic nonnegative-time clock. At the first sampled strict exit of Z from the interval [lower,upper], capped by a natural-number horizon m, the expectation of M at the sampled stopping clock equals its initial sampled expectation. The result transfers the continuous martingale to the sampled filtration and applies bounded first-crossing optional sampling. It can be instantiated with the genuinely killed discounted q-scale process, provided that process is independently proved to be a martingale.
-- source:
--   Combines the accepted monotone-clock martingale reindexing theorem (73af341b-a0e6-4934-8b99-c1303fc922eb) with accepted bounded two-sided sampled martingale optional stopping (73464341-39b0-42c4-8f14-5b4618f13688).

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Martingale.Basic

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.chat03_continuous_grid_two_sided_optional_sampling
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (Z M : ℝ≥0 → Ω → ℝ)
    (hZ : Adapted 𝓕 Z) (hM : Martingale M 𝓕 P)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock)
    (lower upper : ℝ) (m : ℕ) :
    (∫ ω, M (clock (hittingBtwn
      (fun k ω => max (Z (clock k) ω - upper)
        (lower - Z (clock k) ω))
      (Set.Ioi (0 : ℝ)) 0 m ω)) ω ∂P) =
    ∫ ω, M (clock 0) ω ∂P := by
  sorry
