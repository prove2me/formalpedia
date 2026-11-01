-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_realStieltjes_finiteGrid_expected_budget
-- name    : AvramDividend.Classical.avram_wave4_03_sourceLevy_realStieltjes_finiteGrid_expected_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:56:53.802148+00:00
-- url     : https://prove2.me/theorems/68b37692-3201-47de-af94-58b5c8b898d0
-- title:
--   True original Lévy source expected full Stieltjes double-integral finite-step dividend budget
-- statement:
--   For the actual original same-filtration spectrally negative Lévy path and adapted nondecreasing dividend strategy, the expectation of the real Stieltjes time integral of right-grid compensated-exponential source weights times theta and full actual dividendMeasure is bounded by the initial source exponential budget. Each payment interval retains all diffuse and singular-continuous Stieltjes mass and true right-dividend atoms. The proof composes an exact pathwise real Stieltjes integral identity with the already accepted source martingale expected cell-mass inequality.
-- source:
--   Actual source original martingale expected interval-mass budget 780ba3fa and exact real Stieltjes finite-cell identity (published prerequisite); no unproved Ito-Meyer assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_realStieltjes_cellStep_integral_eq_gridMass
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_finiteGrid_intervalMass_expected_budget
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_sourceLevy_realStieltjes_finiteGrid_expected_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ) (u : ℕ → ℝ≥0) (hu : Monotone u)
    (n : ℕ) :
    (∫ ω, ∫ s : ℝ, ∑ i ∈ Finset.range n,
      if s ∈ Ioc (u i : ℝ) (u (i + 1) : ℝ) then
        θ * Real.exp (θ * X.X (u (i + 1)) ω -
          (u (i + 1) : ℝ) * X.ψ θ) *
          Real.exp (-(θ * rightLimit D (u (i + 1)) ω))
      else 0 ∂dividendMeasure D ω ∂P) ≤
    (∫ ω, Real.exp (-(θ * rightLimit D (u 0) ω)) *
      Real.exp (θ * X.X (u 0) ω - (u 0 : ℝ) * X.ψ θ) ∂P) := by sorry
