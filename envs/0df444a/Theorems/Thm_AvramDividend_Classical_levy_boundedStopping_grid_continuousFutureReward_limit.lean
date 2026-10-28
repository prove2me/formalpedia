-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_grid_continuousFutureReward_limit
-- name    : AvramDividend.Classical.levy_boundedStopping_grid_continuousFutureReward_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:51:40.440291+00:00
-- url     : https://prove2.me/theorems/7a69b4fd-57fd-46e3-92e2-5b8dde9e62c4
-- title:
--   Continuous whole-path Lévy future rewards converge along bounded stopped-time grids
-- statement:
--   Under a bounded stopping time and an arbitrary continuous real reward functional of the entire future-increment trajectory (product topology), a common finite adapted upper grid approximates both the stopping time and the reward pointwise. This gives the convergence hypothesis for the bounded-continuous test-function step in proving the strong-Markov product law by limiting finite-grid identities.
-- source:
--   Compose Proved levy_boundedStopping_grid_wholeFuturePath_limit 23c80e32-f74f-42e9-94dc-13d6f0d8e8d9 with continuity of test reward g. Feeds DCT stage of Open strong-Markov 61930a38-11f1-449e-bbb6-67d59c6d5ca8 and barrier child 79978d61-9d1f-4b20-b8a5-114797a8e380. No scale function W.

import Mathlib.Topology.Constructions
import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_grid_wholeFuturePath_limit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_boundedStopping_grid_continuousFutureReward_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbound : ∀ ω, τ ω ≤ T)
    (g : (ℝ≥0 → ℝ) → ℝ) (hg : Continuous g) :
    ∃ (τn : ℕ → Ω → ℝ≥0) (grid : ℕ → Finset ℝ≥0),
      (∀ n ω, τn n ω ∈ grid n) ∧
      (∀ n s, s ∈ grid n →
        MeasurableSet[𝓕 s] {ω : Ω | τn n ω = s}) ∧
      (∀ ω n, τ ω ≤ τn n ω) ∧
      (∀ ω, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω))) ∧
      (∀ ω : Ω,
        Tendsto
          (fun n : ℕ => g (fun t : ℝ≥0 =>
            X.X (τn n ω + t) ω - X.X (τn n ω) ω))
          atTop
          (𝓝 (g (fun t : ℝ≥0 =>
            X.X (τ ω + t) ω - X.X (τ ω) ω)))) := by
  sorry
