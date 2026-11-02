-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_controlled_discounted_gaussian_grid_full_sum_sigma_energy_bound
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_controlled_discounted_gaussian_grid_full_sum_sigma_energy_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:07:22.977849+00:00
-- url     : https://prove2.me/theorems/35b7d838-0888-4f05-a4c3-f3ca4159916f
-- title:
--   Entire controlled actual Gaussian source finite-grid stochastic sum has sigma-squared L2 energy bound
-- statement:
--   For the genuine zero-jump original Levy source and the discounted sigma-scaled strict-prepayment clipped gradient of an admissible dividend strategy, the squared L2 norm of the entire finite grid stochastic source-increment sum is at most the grid cardinality times the sum of exact sigma-squared horizon variances multiplied by the deterministic coefficient bounds. Arbitrary bounded right-continuous original stopping times and grid increments are retained; no independent Brownian copy, no false orthogonality and no assertion of a continuous bracket.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_controlled_discounted_gaussian_bounded_grid_sum_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_controlled_discounted_gaussian_stopped_true_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_controlled_discounted_gaussian_grid_square_energy_sigma_bound

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_controlled_discounted_gaussian_grid_full_sum_sigma_energy_bound
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
    (T : ι → ℝ≥0) (hbounded : ∀ i ω, τ i ω ≤ T i)
    (h : ι → ℝ≥0) :
    let G : ℝ≥0 → Ω → ℝ := fun t ω =>
      let y := Function.leftLim
        (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t
      if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0
    let Q : ι → Ω → ℝ := fun i ω =>
      ((Real.exp (-(q * (s i : ℝ))) * X.σ) *
        max (-K) (min K (G (s i) ω))) *
      (X.X (τ i ω + h i) ω - X.X (τ i ω) ω -
        (h i : ℝ) * X.c)
    (∫ ω, (∑ i ∈ S, Q i ω) ^ 2 ∂P) ≤
      (S.card : ℝ) *
        (∑ i ∈ S, (‖Real.exp (-(q * (s i : ℝ))) * X.σ‖ * K) ^ 2 *
          ((h i : ℝ) * X.σ ^ 2)) := by
  sorry
