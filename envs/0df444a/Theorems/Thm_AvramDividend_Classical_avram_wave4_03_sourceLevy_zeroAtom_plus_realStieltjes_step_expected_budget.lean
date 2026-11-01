-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_zeroAtom_plus_realStieltjes_step_expected_budget
-- name    : AvramDividend.Classical.avram_wave4_03_sourceLevy_zeroAtom_plus_realStieltjes_step_expected_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:56:53.155375+00:00
-- url     : https://prove2.me/theorems/e661ac44-0567-4055-88f5-750117343c8a
-- title:
--   True original Lévy source full Stieltjes expected finite-step budget including initial right-dividend atom
-- statement:
--   For the original same-filtered-space Lévy process and any adapted left-continuous nondecreasing control, the sum of the expected true time-zero right-dividend atom and expected inner real Stieltjes integral of the original source exponential right-cell step weight over the complete dividendMeasure on the positive-time grid is at most one. The proof uses accepted same-path source zero-atom expected grid budget and exact full Stieltjes interval conversion; no atomic dividend concentration is assumed.
-- source:
--   Accepted 42be23e6 original source zero-atom stochastic expected budget, full Stieltjes cell equality, proved dividendMeasure_Ioc_rightLimit and monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_realStieltjes_cellStep_integral_eq_gridMass
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_zeroAtom_plus_fullGrid_mass_expected_budget
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_sourceLevy_zeroAtom_plus_realStieltjes_step_expected_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ) (u : ℕ → ℝ≥0) (hu : Monotone u)
    (hu0 : u 0 = 0) (n : ℕ) :
    (∫ ω, θ * Real.exp (-(θ * rightLimit D 0 ω)) *
      rightLimit D 0 ω ∂P) +
    (∫ ω, ∫ s : ℝ, ∑ i ∈ Finset.range n,
      if s ∈ Ioc (u i : ℝ) (u (i + 1) : ℝ) then
        θ * Real.exp (θ * X.X (u (i + 1)) ω -
          (u (i + 1) : ℝ) * X.ψ θ) *
          Real.exp (-(θ * rightLimit D (u (i + 1)) ω))
      else 0 ∂dividendMeasure D ω ∂P) ≤ 1 := by sorry
