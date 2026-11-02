-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_controlled_discounted_gaussian_bounded_grid_sum_MemLp_two
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_controlled_discounted_gaussian_bounded_grid_sum_MemLp_two
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:27:43.464218+00:00
-- url     : https://prove2.me/theorems/4f1ffa08-7da1-4eb9-a5d4-41d1bb6503a7
-- title:
--   Actual controlled clipped discounted Gaussian source finite-grid stochastic sums are L2
-- statement:
--   On the actual source Lévy probability space with nu=0, admissible adapted dividend control D, C2 test w on the strict-prepayment cap interior and original right-continuous filtration, every finite sum of clipped discounted sigma-scaled predictable-gradient coefficients multiplied by true bounded-stopped drift-centred source increments is MemLp 2. The time grids and stopping times may vary over finite indices and all calculations use X itself. This is the finite simple stochastic-sum existence/localisation interface, not an expectation-zero or Ito quadratic-variation result.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_controlled_discounted_gaussian_stopped_true_increment_MemLp_two

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_controlled_discounted_gaussian_bounded_grid_sum_MemLp_two
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
    MemLp (fun ω => ∑ i ∈ S,
      ((Real.exp (-(q * (s i : ℝ))) * X.σ) *
          max (-K) (min K (G (s i) ω))) *
      (X.X (τ i ω + h i) ω - X.X (τ i ω) ω -
        (h i : ℝ) * X.c)) 2 P := by
  sorry
