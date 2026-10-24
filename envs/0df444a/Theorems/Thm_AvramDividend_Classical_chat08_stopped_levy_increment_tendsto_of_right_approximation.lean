-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_stopped_levy_increment_tendsto_of_right_approximation
-- name    : AvramDividend.Classical.chat08_stopped_levy_increment_tendsto_of_right_approximation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-23T23:42:06.59711+00:00
-- url     : https://prove2.me/theorems/8f73cd3f-a954-42f0-8b97-1d2f9f66b949
-- title:
--   Stopping-time approximation from above preserves shifted Lévy increments pathwise
-- statement:
--   For random nonnegative times T_n(ω) that converge to τ(ω) from above on every sample path, the increment X(T_n(ω)+u,ω)−X(T_n(ω),ω) converges to X(τ(ω)+u,ω)−X(τ(ω),ω). This lifts the accepted deterministic-time-approximation result pointwise and prepares the finite-valued stopping-time-to-general-stopping-time limit in the strong Markov proof.
-- source:
--   Prove2Me chat08_levy_increment_tendsto_of_right_approximated_times.

import Mathlib.Topology.NhdsWithin
import Theorems.Thm_AvramDividend_Classical_chat08_levy_increment_tendsto_of_right_approximated_times

open Filter MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.chat08_stopped_levy_increment_tendsto_of_right_approximation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (T : ℕ → Ω → ℝ≥0) (τ : Ω → ℝ≥0) (u : ℝ≥0)
    (hT : ∀ ω, Tendsto (fun n => T n ω) atTop (𝓝 (τ ω)))
    (habove : ∀ ω n, τ ω ≤ T n ω) :
    ∀ ω, Tendsto
      (fun n => X.X (T n ω + u) ω - X.X (T n ω) ω)
      atTop (𝓝 (X.X (τ ω + u) ω - X.X (τ ω) ω)) := by sorry
