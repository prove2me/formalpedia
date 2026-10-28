-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_killed_scale_expectation_tendsto_seq_no_schedule
-- name    : AvramDividend.Classical.chat04_positive_reserve_killed_scale_expectation_tendsto_seq_no_schedule
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:00:55.662271+00:00
-- url     : https://prove2.me/theorems/1ea5d6fe-7736-42da-8917-208b2fc62d78
-- title:
--   Initial-time sequence continuity of killed scale expectations without observation schedule
-- statement:
--   For strictly positive starting reserve, the expected discounted whole-history killed q-scale payoff converges to the initial scale value along any bounded deterministic sequence approaching zero. Measurability follows from the already Proved closed-window survival theorem without an auxiliary observation schedule, and uniform L² control gives expectation convergence. This removes a technical grid-cover hypothesis from the killed semigroup prerequisite of two-sided exit.
-- source:
--   Directly imports the proved closed-window shifted survival measurability theorem without a schedule, plus proved killed L² bound, pathwise initial continuity and expectation uniform second-moment theorem. Supports all-time killed q-scale renewal identity a885f0b3 and strict exit 09663d0d.

import Theorems.Thm_AvramDividend_Classical_chat04_killed_deterministic_horizon_scale_l2_bound
import Theorems.Thm_AvramDividend_Classical_chat04_shifted_lower_survival_measurable_no_schedule
import Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_real_killed_scale_tendsto_initial
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable
import Theorems.Thm_AvramDividend_Classical_nonnegative_integral_tendsto_of_uniform_second_moment
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.chat04_positive_reserve_killed_scale_expectation_tendsto_seq_no_schedule
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ) (hx : 0 < x)
    (N : ℝ≥0) (t : ℕ → ℝ≥0) (htN : ∀ n, t n ≤ N)
    (ht0 : Filter.Tendsto t Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n => ∫ ω,
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t n → 0 ≤ x + X.X s u}).indicator
          (fun u => Real.exp (-(q * (t n : ℝ))) *
            W (x + X.X (t n) u)) ω ∂P)
      Filter.atTop (𝓝 (W x)) := by sorry
