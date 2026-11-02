-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_true_increment_quotient_L2_convergence
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_true_increment_quotient_L2_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:42:03.777185+00:00
-- url     : https://prove2.me/theorems/1d57e9ea-84ed-44d4-825c-3381c9dc260e
-- title:
--   Original stopped Gaussian quotient converges to true centred increment in squared L2
-- statement:
--   The genuine same-path positive-parameter exponential Gaussian source quotient converges to the true stopped drift-centred source increment in L2 squared error in the original probability space. The Proved Fatou error bound is squeezed between zero and an exponential quadratic secant excess tending to zero as parameter theta tends to zero from the right. This is a source-faithful quantitative bridge towards exact sigma-squared variance and Ito quadratic variation; nu=0, bounded original right-continuous stopping time, sigma=0 allowed, no detached Brownian.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_fixed_quotient_fatou_error_le
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_exp_quadratic_secant_right_limit

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_true_increment_quotient_L2_convergence
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) :
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    let Z : ℝ → Ω → ℝ := fun ξ ω =>
      (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ ξ) - 1) / ξ
    Filter.Tendsto
      (fun θ : ℝ => (∫⁻ ω, ENNReal.ofReal ((Z θ ω - Y ω) ^ 2) ∂P))
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
  sorry
