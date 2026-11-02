-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_controlled_discounted_gaussian_finite_grid_localized_mean_zero
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_controlled_discounted_gaussian_finite_grid_localized_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:27:12.660121+00:00
-- url     : https://prove2.me/theorems/e6be07db-7ebd-4a40-8dfd-b7816cce1790
-- title:
--   Actual discounted controlled strict-prepayment Gaussian gradient has zero-mean localized source finite grids
-- statement:
--   For the actual SpectrallyNegativeLevy source X with ν=0, any admissible original-filtration dividend D, C² HJB test w on the strict capped interior, finite source time grid, discount q and finite gradient clipping threshold K≥0, the compensated Gaussian exponential quotient simple stochastic integral with coefficient exp(-q s_i)σ clipped[deriv w of the exact prepayment reserve left limit] has expectation zero. Uses the Proved original source right-continuous Lévy lift and predictable finite-grid centred exponential theorem, along with canonical controlled-prejump-gradient IsStronglyPredictable and clipping. It transports the exact controlled integrand and discount to the genuine source finite-grid martingale approximation without a Brownian copy. The full continuous stochastic integral and Ito-Meyer identity remain open.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_prejump_cap_gradient_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_clipped_stronglyPredictable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_gaussian_predictable_finite_grid_mean_zero

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_controlled_discounted_gaussian_finite_grid_localized_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (S : Finset ι) (s t : ι → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (q K θ : ℝ) (hK : 0 ≤ K) (hθ : 0 ≤ θ) :
    let G : ℝ≥0 → Ω → ℝ := fun t ω =>
      let y := Function.leftLim
        (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t
      if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0
    let H : ι → Ω → ℝ := fun i ω =>
      (Real.exp (-(q * (s i : ℝ))) * X.σ) *
        max (-K) (min K (G (s i) ω))
    (∫ ω, ∑ i ∈ S, H i ω *
      ((Real.exp (θ * (X.X (t i) ω - X.X (s i) ω) -
        ((t i - s i : ℝ≥0) : ℝ) * X.ψ θ) - 1) / θ) ∂P) = 0 := by
  sorry
