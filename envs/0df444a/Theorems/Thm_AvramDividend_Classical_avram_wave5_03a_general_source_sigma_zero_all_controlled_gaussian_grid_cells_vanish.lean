-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_general_source_sigma_zero_all_controlled_gaussian_grid_cells_vanish
-- name    : AvramDividend.Classical.avram_wave5_03a_general_source_sigma_zero_all_controlled_gaussian_grid_cells_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:43:27.936519+00:00
-- url     : https://prove2.me/theorems/711402f8-e4a0-4307-9a7d-e8ad5af34ff1
-- title:
--   When sigma is zero all actual controlled Gaussian finite-grid stochastic sums vanish for arbitrary Levy jumps
-- statement:
--   For any original spectrally negative Levy source with arbitrary jump measure and sigma zero, actual admissible dividend control and strict-prepayment clipped discounted reserve-gradient coefficients, every finite grid sum against the original drift-centred source increments vanishes pointwise. This is the exact source-integral absence statement in the general jump root branch; it does not impose nu=0, continuity or Gaussian positivity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_general_source_sigma_zero_all_controlled_gaussian_grid_cells_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hσ : X.σ = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (S : Finset ι) (s : ι → ℝ≥0) (q K : ℝ)
    (τ : ι → Ω → ℝ≥0) (h : ι → ℝ≥0) :
    let G : ℝ≥0 → Ω → ℝ := fun t ω =>
      let y := Function.leftLim
        (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t
      if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0
    ∀ ω : Ω, (∑ i ∈ S,
      ((Real.exp (-(q * (s i : ℝ))) * X.σ) *
        max (-K) (min K (G (s i) ω))) *
      (X.X (τ i ω + h i) ω - X.X (τ i ω) ω -
        (h i : ℝ) * X.c)) = 0 := by
  sorry
