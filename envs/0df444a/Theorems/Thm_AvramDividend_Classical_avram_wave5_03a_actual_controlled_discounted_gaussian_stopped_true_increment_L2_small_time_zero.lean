-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_controlled_discounted_gaussian_stopped_true_increment_L2_small_time_zero
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_controlled_discounted_gaussian_stopped_true_increment_L2_small_time_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T12:26:25.43+00:00
-- url     : https://prove2.me/theorems/a27a102a-73e1-4e6b-9b2a-6dac681bdea9
-- title:
--   Exact discounted controlled Gaussian source increment has L2-continuous small stopped horizon
-- statement:
--   For the genuine zero-jump Lévy process X, an adapted admissible dividend strategy D, compact-cap-interior C² HJB test w, original right-continuous bounded stopping time τ, and exact clipped strict-prepayment left-limit reserve gradient G, the squared expectation of H_s(X_(τ+h)-Xτ-hc) tends to zero as h↓0, where H_s=exp(-qs)σ clip_K G_s. This directly transports canonically Proved same-path Gaussian stopped weighted small-time L2 continuity using original-filtration predictability; σ may vanish. This is a genuine controlled source stochastic-integral localisation cell, not a Brownian representation or full Ito-Meyer identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_prejump_cap_gradient_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_clipped_stronglyPredictable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_weighted_true_increment_L2_small_time_zero

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_controlled_discounted_gaussian_stopped_true_increment_L2_small_time_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (s : ℝ≥0) (q K : ℝ) (hK : 0 ≤ K)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T) :
    let G : ℝ≥0 → Ω → ℝ := fun t ω =>
      let y := Function.leftLim
        (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t
      if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0
    let H : Ω → ℝ := fun ω =>
      (Real.exp (-(q * (s : ℝ))) * X.σ) *
        max (-K) (min K (G s ω))
    Filter.Tendsto
      (fun h : ℝ≥0 =>
        (∫ ω, (H ω *
          (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c)) ^ 2 ∂P))
      (𝓝 (0 : ℝ≥0)) (𝓝 (0 : ℝ)) := by
  sorry
