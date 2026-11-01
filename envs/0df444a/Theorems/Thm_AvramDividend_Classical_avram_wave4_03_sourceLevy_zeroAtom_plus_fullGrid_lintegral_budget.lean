-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_zeroAtom_plus_fullGrid_lintegral_budget
-- name    : AvramDividend.Classical.avram_wave4_03_sourceLevy_zeroAtom_plus_fullGrid_lintegral_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:11:21.18211+00:00
-- url     : https://prove2.me/theorems/11934d73-3220-46a7-8343-3acd1c020d8a
-- title:
--   Original Lévy true initial atom plus full Stieltjes finite-grid cash ENNReal expected budget
-- statement:
--   On the actual Lévy filtered probability space and for any adapted left-continuous strategy D, the expected ENNReal sum of the genuinely time-zero right dividend atom and all positive-time finite-grid full Stieltjes cash is ≤1. The proof uses genuine source cash L1 and real expected budget, then exact ENNReal conversion; no countable-atomic assumption.
-- source:
--   Proved same-process initial atom real stochastic expected budget 42be23e6, genuine finite-grid L1 668c8640, original cash nonneg 3397f585, and new initial atom L1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_initial_rightAtom_discountedCash_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_finiteGrid_fullStieltjes_cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_sourceLevy_finiteGrid_discounted_dividend_mass_expectation_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_zeroAtom_plus_fullGrid_mass_expected_budget
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_sourceLevy_zeroAtom_plus_fullGrid_lintegral_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ) (u : ℕ → ℝ≥0) (hu : Monotone u)
    (hu0 : u 0 = 0) (n : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (θ * Real.exp (-(θ * rightLimit D 0 ω)) *
      rightLimit D 0 ω) ∂P) +
    (∫⁻ ω, ENNReal.ofReal (θ * ∑ i ∈ Finset.range n,
      Real.exp (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ) *
      Real.exp (-(θ * rightLimit D (u (i + 1)) ω)) *
      (rightLimit D (u (i + 1)) ω - rightLimit D (u i) ω)) ∂P) ≤ 1 := by sorry
