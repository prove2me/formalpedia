-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_killed_scale_expectation_tendsto_seq
-- name    : AvramDividend.Classical.chat04_positive_reserve_killed_scale_expectation_tendsto_seq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T14:40:40.180511+00:00
-- url     : https://prove2.me/theorems/0e28c869-8621-4314-a927-e9bb7bc879dc
-- title:
--   Time-zero convergence of expected history-killed q-scale rewards
-- statement:
--   For strictly positive initial reserve and deterministic bounded time observations approaching zero, the expectation of the discounted q-scale payoff killed when the entire path first goes below zero converges to W(x). Measurability of the closed-horizon path event follows from a reciprocal-grid covering schedule. Pointwise convergence of the killed real payoff, together with an explicit uniform L² bound, yields convergence of expectations by an existing Proved uniform-second-moment theorem. This is the correct history-killed initial-time bridge for the unbounded-variation q-scale renewal identity, which remains the main stochastic prerequisite to the two-sided exit identity.
-- source:
--   Imports Proved/targeted chat04_killed_deterministic_horizon_scale_l2_bound 294fb6fa; shifted_lower_survival_measurable 33f5f781; real_killed_scale_tendsto_initial f371a1e3; nonnegative_integral_tendsto_of_uniform_second_moment bef79c38. Next Open killed semigroup harmonicity a885f0b3 and strict exit 09663d0d.

import Theorems.Thm_AvramDividend_Classical_chat04_killed_deterministic_horizon_scale_l2_bound
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_lower_survival_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_real_killed_scale_tendsto_initial
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable
import Theorems.Thm_AvramDividend_Classical_nonnegative_integral_tendsto_of_uniform_second_moment
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.chat04_positive_reserve_killed_scale_expectation_tendsto_seq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ) (hx : 0 < x)
    (N : ℝ≥0) (t : ℕ → ℝ≥0) (htN : ∀ n, t n ≤ N)
    (ht0 : Filter.Tendsto t Filter.atTop (𝓝 0)) :
    Filter.Tendsto
      (fun n => ∫ ω,
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t n → 0 ≤ x + X.X s u}).indicator
          (fun u => Real.exp (-(q * (t n : ℝ))) *
            W (x + X.X (t n) u)) ω ∂P)
      Filter.atTop (𝓝 (W x)) := by sorry
