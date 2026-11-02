-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_controlled_discounted_gaussian_grid_square_energy_sigma_bound
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_controlled_discounted_gaussian_grid_square_energy_sigma_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:33:45.803516+00:00
-- url     : https://prove2.me/theorems/acfd9136-f0a4-4ffd-80e4-24e7ed0b55bb
-- title:
--   Actual controlled Gaussian finite-grid expected quadratic energy has correct sigma-squared upper bound
-- statement:
--   For the original zero-jump Gaussian Levy source X and actual adapted admissible dividend strategy, on each bounded original rightCont stopping interval the strict-prepayment C2 reserve gradient clipped by K and weighted by exp(-qs) sigma has original-source true drift-centred increment squared energy bounded by the precise sigma squared convention. Integrability and linearity show the expected sum of squared controlled Gaussian cells is at most the corresponding sum of sigma squared weighted horizon costs. This is finite-grid quadratic energy control, not the quadratic variation/bracket identity or a full Ito rule.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_controlled_discounted_gaussian_stopped_true_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_controlled_discounted_gaussian_stopped_true_increment_sigma_energy_bound

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_controlled_discounted_gaussian_grid_square_energy_sigma_bound
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
    (∫ ω, ∑ i ∈ S, (Q i ω) ^ 2 ∂P) ≤
      ∑ i ∈ S,
        (‖Real.exp (-(q * (s i : ℝ))) * X.σ‖ * K) ^ 2 *
          ((h i : ℝ) * X.σ ^ 2) := by
  sorry
