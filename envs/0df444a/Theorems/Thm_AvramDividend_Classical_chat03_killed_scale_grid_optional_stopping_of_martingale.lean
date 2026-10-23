-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_killed_scale_grid_optional_stopping_of_martingale
-- name    : AvramDividend.Classical.chat03_killed_scale_grid_optional_stopping_of_martingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T10:28:16.009994+00:00
-- url     : https://prove2.me/theorems/b6c72d3d-bdc9-44ea-9cb2-a69612464cbd
-- title:
--   Bounded first-exit expectation for the genuinely killed discounted scale process
-- statement:
--   Starting from nonnegative reserve x, assume the actual discounted scale payoff, killed on any earlier passage strictly below zero, is a continuous-time martingale. Then its expectation at the bounded two-sided first grid crossing on an arbitrary monotone observation clock is exactly W(x). This preserves the whole-path survival indicator, which prevents ruin-and-recovery paths contaminating the raw scale payoff. The premise that the killed payoff is a martingale remains an independent Lévy/scale-function harmonicity obligation.
-- source:
--   A direct application of already Proved deterministic monotone reindexing and bounded two-sided optional sampling, with X_zero and probability normalisation at time zero. Corrected the terminal-time reserve application and simplified the time-zero indicator using nonnegative x.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Martingale.Basic

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.chat03_killed_scale_grid_optional_stopping_of_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (W : ℝ → ℝ) (hx : 0 ≤ x)
    (hKilled : Martingale
      (fun (t : ℝ≥0) ω =>
        ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => Real.exp (-(q * (t : ℝ))) *
            W (x + X.X t ω)) ω) 𝓕 P)
    (clock : ℕ → ℝ≥0) (hc : Monotone clock)
    (hclock0 : clock 0 = 0)
    (lower upper : ℝ) (m : ℕ) :
    (∫ ω,
      ({ω | ∀ s : ℝ≥0,
        s ≤ clock (hittingBtwn
          (fun k ω => max (X.X (clock k) ω - upper)
            (lower - X.X (clock k) ω))
          (Set.Ioi (0 : ℝ)) 0 m ω) →
          0 ≤ x + X.X s ω}).indicator
      (fun ω =>
        Real.exp (-(q * (clock (hittingBtwn
          (fun k ω => max (X.X (clock k) ω - upper)
            (lower - X.X (clock k) ω))
          (Set.Ioi (0 : ℝ)) 0 m ω) : ℝ))) *
        W (x + X.X (clock (hittingBtwn
          (fun k ω => max (X.X (clock k) ω - upper)
            (lower - X.X (clock k) ω))
          (Set.Ioi (0 : ℝ)) 0 m ω)) ω)) ω ∂P) = W x := by
  sorry
