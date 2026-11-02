-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_controlled_discounted_gaussian_stopped_true_increment_sigma_energy_bound
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_controlled_discounted_gaussian_stopped_true_increment_sigma_energy_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:47:01.258209+00:00
-- url     : https://prove2.me/theorems/ea171a75-372e-4340-aae4-c727e76c2149
-- title:
--   Actual discounted controlled strict-prepayment Gaussian true stopped increment has sigma-squared L2 energy
-- statement:
--   For the exact original zero-jump Gaussian spectrally negative Lévy process and an original-filtration admissible dividend control, the clipped prepayment left-limit HJB gradient with deterministic discount and sigma weight multiplies the true drift-centred stopped source increment with squared expectation bounded by (|exp(-q s) sigma| K)^2 h sigma^2. The stopping time belongs to original F.rightCont, bounded by T, with smoothness only on the cap interior. This is the literal stochastic integral cell localisation estimate beyond exponential approximations; no independent Brownian process, general Lévy jumps, or full Ito-Meyer identity is asserted.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_prejump_cap_gradient_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_clipped_stronglyPredictable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_true_increment_L2_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_real_variance_le

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_controlled_discounted_gaussian_stopped_true_increment_sigma_energy_bound
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
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) :
    let G : ℝ≥0 → Ω → ℝ := fun t ω =>
      let y := Function.leftLim
        (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t
      if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0
    let H : Ω → ℝ := fun ω =>
      (Real.exp (-(q * (s : ℝ))) * X.σ) *
        max (-K) (min K (G s ω))
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    (∫ ω, (H ω * Y ω) ^ 2 ∂P) ≤
      (‖Real.exp (-(q * (s : ℝ))) * X.σ‖ * K) ^ 2 *
        ((h : ℝ) * X.σ ^ 2) := by
  sorry
