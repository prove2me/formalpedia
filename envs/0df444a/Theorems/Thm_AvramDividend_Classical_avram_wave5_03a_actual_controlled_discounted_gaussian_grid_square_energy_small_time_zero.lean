-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_controlled_discounted_gaussian_grid_square_energy_small_time_zero
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_controlled_discounted_gaussian_grid_square_energy_small_time_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:46:30.286536+00:00
-- url     : https://prove2.me/theorems/f8bc8e16-1638-43e6-b9da-60b96d5adbfb
-- title:
--   Actual discounted controlled prepayment Gaussian finite-grid squared energy vanishes for shrinking common horizon
-- statement:
--   For the genuine zero-jump Gaussian SpectrallyNegativeLevy source and actual adapted dividend strategy, the finite sum of squares of the discounted sigma-scaled clipped strict-prepayment gradient coefficients times genuine stopped drift-centred source increments has expectation tending to zero when the common time horizon h tends to zero. The original right-continuous stopping times are each bounded; no Brownian copy is used. This is a controlled finite-grid stochastic localisation limit, not a continuous bracket or Ito identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_controlled_discounted_gaussian_stopped_true_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_controlled_discounted_gaussian_stopped_true_increment_L2_small_time_zero

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_controlled_discounted_gaussian_grid_square_energy_small_time_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (S : Finset ι) (s : ι → ℝ≥0) (q K : ℝ) (hK : 0 ≤ K)
    (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i, IsStoppingTime 𝓕.rightCont (fun ω => (τ i ω : WithTop ℝ≥0)))
    (T : ι → ℝ≥0) (hbounded : ∀ i ω, τ i ω ≤ T i) :
    let G : ℝ≥0 → Ω → ℝ := fun t ω =>
      let y := Function.leftLim
        (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t
      if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0
    Filter.Tendsto (fun h : ℝ≥0 =>
      (∫ ω, ∑ i ∈ S,
        (((Real.exp (-(q * (s i : ℝ))) * X.σ) *
            max (-K) (min K (G (s i) ω))) *
          (X.X (τ i ω + h) ω - X.X (τ i ω) ω -
            (h : ℝ) * X.c)) ^ 2 ∂P))
      (𝓝 (0 : ℝ≥0)) (𝓝 (0 : ℝ)) := by
  sorry
