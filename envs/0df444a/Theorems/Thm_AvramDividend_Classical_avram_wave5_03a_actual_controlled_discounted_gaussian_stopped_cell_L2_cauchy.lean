-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_controlled_discounted_gaussian_stopped_cell_L2_cauchy
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_controlled_discounted_gaussian_stopped_cell_L2_cauchy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:23:39.061455+00:00
-- url     : https://prove2.me/theorems/29e8968c-dda7-4d52-be90-d0fc661b37cf
-- title:
--   Actual controlled discounted strict-prepayment Gaussian source cell has L2 Cauchy approximation
-- statement:
--   For the original zero-jump spectrally negative Levy source X with admissible original-filtration dividend control D and a C2 test function w on the strictly interior reserve region, the exact discounted clipped Gaussian derivative coefficient exp(-q*s)*sigma*clip(deriv w at the left-limit prepayment controlled reserve) multiplies same-source stopped Gaussian exponential quotients. For any bounded right-continuous source stopping time and two positive null quotient parameter sequences, the expectation of the square of the difference of these weighted quotients converges to zero. This is a genuine controlled source one-cell stochastic integral localization, using Proved prepayment-gradient strong predictability and bounded clipping and Proved source bounded-multiplier L2 Cauchy. No Brownian copy, source bracket process or full Ito-Meyer formula is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_prejump_cap_gradient_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_clipped_stronglyPredictable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_multiplier_L2_cauchy

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_controlled_discounted_gaussian_stopped_cell_L2_cauchy
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
    (h : ℝ≥0)
    (θ η : ℕ → ℝ)
    (hθ : Filter.Tendsto θ atTop (𝓝[>] (0 : ℝ)))
    (hη : Filter.Tendsto η atTop (𝓝[>] (0 : ℝ))) :
    let G : ℝ≥0 → Ω → ℝ := fun t ω =>
      let y := Function.leftLim
        (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t
      if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0
    let H : Ω → ℝ := fun ω =>
      (Real.exp (-(q * (s : ℝ))) * X.σ) *
        max (-K) (min K (G s ω))
    let Z : ℝ → Ω → ℝ := fun ξ ω =>
      (Real.exp (ξ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ ξ) - 1) / ξ
    Filter.Tendsto (fun n : ℕ =>
      (∫ ω, (H ω * (Z (θ n) ω - Z (η n) ω)) ^ 2 ∂P))
      atTop (𝓝 (0 : ℝ)) := by
  sorry
