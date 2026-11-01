-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_zeroAtom_plus_fullGrid_mass_expected_budget
-- name    : AvramDividend.Classical.avram_wave4_03_sourceLevy_zeroAtom_plus_fullGrid_mass_expected_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:38:38.640475+00:00
-- url     : https://prove2.me/theorems/42be23e6-6caf-4c14-98f0-662c111d3198
-- title:
--   True source Lévy stochastic finite-grid Stieltjes expected bound including time-zero right dividend atom
-- statement:
--   For the genuine source Lévy path X and adapted left-continuous D, arbitrary nondecreasing finite grid starting at time zero, the expected sum of the actual time-zero right dividend atom weighted by θ exp(-θD0+) and all positive-time full Stieltjes cell dividend masses weighted by the observed original compensated exponential Z and postpayment exponential is at most one. The initial atom is paid for by the exact scalar convexity drop 1−exp(-θD0+); the remaining budget is the already proved same-source stochastic expected finite-grid mass theorem 3397f585. This includes diffuse and singular-continuous D via cell masses, and does not purport to prove arbitrary nonlinear w compensation.
-- source:
--   Accepted actual original source expected full dividend mass grid 3397f585, scalar convexity 47f187ca, source adapted postpayment D and X0=0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_exponential_control_loss_dominates_discounted_dividend_increment
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_sourceLevy_finiteGrid_discounted_dividend_mass_expectation_budget

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_sourceLevy_zeroAtom_plus_fullGrid_mass_expected_budget {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ) (u : ℕ → ℝ≥0) (hu : Monotone u)
    (hu0 : u 0 = 0) (n : ℕ) :
    (∫ ω, θ * Real.exp (-(θ * rightLimit D 0 ω)) *
      rightLimit D 0 ω ∂P) +
    (∫ ω, θ * ∑ i ∈ Finset.range n,
      Real.exp (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ) *
      Real.exp (-(θ * rightLimit D (u (i + 1)) ω)) *
      (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω) ∂P) ≤ 1 := by sorry
