-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_finiteGrid_fullStieltjes_doubleLintegral_budget
-- name    : AvramDividend.Classical.avram_wave4_03_sourceLevy_finiteGrid_fullStieltjes_doubleLintegral_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:02:23.428976+00:00
-- url     : https://prove2.me/theorems/e8f0e18c-a96e-46a5-ae30-6608d9587554
-- title:
--   Original Lévy actual expected full Stieltjes double integral finite-grid inequality
-- statement:
--   For the same original source Lévy process X and adapted finite variation controlled dividend D, the expected double Lebesgue/Stieltjes integral of the full right-grid step exponential cash density is bounded by original initial postpayment martingale wealth. Both diffuse and atomic Stieltjes dividends occur in the exact measure integral. This is a genuine stochastic finite-step estimate in the original probability space and a directly applicable antecedent for the proved double-Fatou limit.
-- source:
--   Accepted pathwise exact full-Stieltjes finite-cell identity 8358e91d and original ENNReal expected finite-grid budget pending integrability; no independent-source law substitution.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_fullStieltjes_cellIntegral_eq_finiteGrid_cashENNReal
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_finiteGrid_fullStieltjes_lintegral_budget
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_sourceLevy_finiteGrid_fullStieltjes_doubleLintegral_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ) :
    (∫⁻ ω, ∫⁻ s : ℝ, ∑ i ∈ Finset.range n,
      if s ∈ Ioc (u i : ℝ) (u (i + 1) : ℝ) then
        ENNReal.ofReal (θ *
          Real.exp (θ * X.X (u (i + 1)) ω -
            (u (i + 1) : ℝ) * X.ψ θ) *
          Real.exp (-(θ * rightLimit D (u (i + 1)) ω)))
      else 0 ∂dividendMeasure D ω ∂P) ≤
    ENNReal.ofReal (∫ ω,
      Real.exp (-(θ * rightLimit D (u 0) ω)) *
      Real.exp (θ * X.X (u 0) ω - (u 0 : ℝ) * X.ψ θ) ∂P) := by sorry
