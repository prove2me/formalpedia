-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_grid_ennrealFutureReward_limit
-- name    : AvramDividend.Classical.levy_boundedStopping_grid_ennrealFutureReward_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T12:11:04.821437+00:00
-- url     : https://prove2.me/theorems/102ad9e0-7be0-40a0-896c-316e86d9b222
-- title:
--   Nonnegative Lévy future rewards converge along bounded stopping grids
-- statement:
--   Under a bounded stopping-time hypothesis, one finite adapted upper grid converges pathwise to the stopped time and simultaneously preserves pointwise convergence of any continuous nonnegative extended-real reward of the entire Lévy future-increment path. This gives the exact reward codomain used by nonnegative dividend integrals in the limiting strong-Markov argument.
-- source:
--   Composes Proved whole-path grid convergence 23c80e32-f74f-42e9-94dc-13d6f0d8e8d9 with continuity of g. Unlike real-valued result 7a69b4fd-57fd-46e3-92e2-5b8dde9e62c4 this has ℝ≥0∞ codomain, matching the stopped-grid reward decomposition and Fatou/DCT bridge required by strong Markov 61930a38-11f1-449e-bbb6-67d59c6d5ca8 and W-free child 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.Topology.Constructions
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_grid_wholeFuturePath_limit

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_boundedStopping_grid_ennrealFutureReward_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbound : ∀ ω, τ ω ≤ T)
    (g : (ℝ≥0 → ℝ) → ℝ≥0∞) (hg : Continuous g) :
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
