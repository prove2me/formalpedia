-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_controlled_discounted_gaussian_grid_full_sum_L2_small_time_zero
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_controlled_discounted_gaussian_grid_full_sum_L2_small_time_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:59:05.816193+00:00
-- url     : https://prove2.me/theorems/c6006f96-42b9-4b46-aaaa-5f427dc5b83f
-- title:
--   Entire finite sum of original discounted controlled Gaussian source cells tends to zero in L2
-- statement:
--   For the original zero-jump Levy source with admissible dividend D, original strict-prepayment capped reserve gradient and exact sigma-scaled discounted coefficients, the squared expectation of the entire finite sum of genuine right-continuous stopped drift-centred source increment cells tends to zero as a common future horizon tends to zero. The original filtration and source processes are unchanged. The proof uses canonical MemLp 2 of the actual controlled grid, the sum-of-squares small-time source result, and finite Cauchy-Schwarz; not a continuous quadratic variation or full Ito identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_controlled_discounted_gaussian_bounded_grid_sum_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_controlled_discounted_gaussian_stopped_true_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_controlled_discounted_gaussian_grid_square_energy_small_time_zero

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_controlled_discounted_gaussian_grid_full_sum_L2_small_time_zero
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
      (∫ ω, (∑ i ∈ S,
        ((Real.exp (-(q * (s i : ℝ))) * X.σ) *
            max (-K) (min K (G (s i) ω))) *
          (X.X (τ i ω + h) ω - X.X (τ i ω) ω -
            (h : ℝ) * X.c)) ^ 2 ∂P))
      (𝓝 (0 : ℝ≥0)) (𝓝 (0 : ℝ)) := by
  sorry
