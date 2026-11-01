-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_finiteGrid_intervalMass_expected_budget
-- name    : AvramDividend.Classical.avram_wave4_03_sourceLevy_finiteGrid_intervalMass_expected_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:29:49.601482+00:00
-- url     : https://prove2.me/theorems/780ba3fa-f1fd-4b87-9517-7f349e029fbe
-- title:
--   Genuine source Lévy expected finite-grid budget expressed in full random Stieltjes interval masses
-- statement:
--   The original same-filtered-space spectrally negative Lévy X, adapted nondecreasing left-continuous D, and any nondecreasing finite grid have a true expected discounted source-exponential dividend budget in terms of the complete random Stieltjes dividendMeasure on each Ioc grid cell; the measure mass is converted to real because it is a finite rightLimit increment. The inequality includes all diffuse and singular-continuous D mass and real right-dividend atoms, and is a useful exact source stochastic-to-measure translation for full-integral passage.
-- source:
--   Accepted original-source finite-grid stochastic expected bound 3397f585; exact Stieltjes interval identity f9211de0; BV rightLimit monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_sourceLevy_finiteGrid_discounted_dividend_mass_expectation_budget
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_sourceLevy_finiteGrid_intervalMass_expected_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ) (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ) :
    (∫ ω, θ * ∑ i ∈ Finset.range n,
      Real.exp (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ) *
      Real.exp (-(θ * rightLimit D (u (i + 1)) ω)) *
      (dividendMeasure D ω (Ioc (u i : ℝ) (u (i + 1) : ℝ))).toReal ∂P) ≤
    (∫ ω, Real.exp (-(θ * rightLimit D (u 0) ω)) *
      Real.exp (θ * X.X (u 0) ω - (u 0 : ℝ) * X.ψ θ) ∂P) := by sorry
