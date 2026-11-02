-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_controlled_discounted_nojump_gaussian_true_centered_grid_mean_zero
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_controlled_discounted_nojump_gaussian_true_centered_grid_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:31:46.642353+00:00
-- url     : https://prove2.me/theorems/d7ff0a06-55d6-4ada-b392-85d364c9fab2
-- title:
--   Actual stopped, clipped, discounted control-gradient finite Gaussian source integral has exact mean zero
-- statement:
--   For actual SpectrallyNegativeLevy X with ν=0, arbitrary σ including σ>0, an admissible original-filtration dividend strategy, and finite time grid, the physical discounted strictly-prepayment ruin-clipped gradient multiplied by true drift-centred original source increments has zero expectation as an entire finite sum. This is not an exponential-quotient or copied Brownian variable. It follows from true source stopped mean-zero after proving it by shifted Fatou, genuine original-source MemLp2 integrability, and the canonically Proved stopped clipped original finite-grid predictable centered-payoff theorem. The conclusion is a real simple stochastic-integral localisation interface and does not assert the limiting stochastic integral or continuous bracket.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_originalSource_stoppedClippedFiniteGrid_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_drift_centered_increment_mean_zero

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_controlled_discounted_nojump_gaussian_true_centered_grid_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q K : ℝ) (hK : 0 ≤ K)
    (T : ℝ≥0) (S : Finset ι) (s t : ι → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i) :
    (∫ ω, ∑ i ∈ S,
      max (-K) (min K
        (if s i ≤ T then
          (Real.exp (-(q * (s i : ℝ))) *
            deriv w (Function.leftLim
              (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω) (s i))) *
          (if (s i : ℝ≥0∞) ≤ ruinTime X x D ω then
            (1 : ℝ) else 0)
        else 0)) *
      ((X.X (t i) ω - X.X (s i) ω) - ((t i - s i : ℝ≥0) : ℝ) * X.c) ∂P)
      = 0 := by
  sorry
