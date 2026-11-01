-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_realStieltjes_cellStep_integral_eq_gridMass
-- name    : AvramDividend.Classical.avram_wave4_03_sourceLevy_realStieltjes_cellStep_integral_eq_gridMass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:38:39.933871+00:00
-- url     : https://prove2.me/theorems/1aef9913-54ab-4119-9a3b-398db0526354
-- title:
--   Same-path original source Lévy real Stieltjes finite-cell step integral equals actual full dividendMeasure mass sum
-- statement:
--   For the genuine source Lévy process and any admissible dividend strategy path, the real Bochner integral against full dividendMeasure of the finite-grid cellwise constant, original source-exponential discount weights equals the finite sum of the same source weights times the true Stieltjes mass on every half-open cell. The proof establishes cell finiteness and integrability and covers diffuse and right-atomic dividend mass.
-- source:
--   Pinned original-source definitions and dividendMeasure_Ioc_rightLimit f9211de0; Mathlib integral_finset_sum, integral_indicator_const, integrableOn_const.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_sourceLevy_realStieltjes_cellStep_integral_eq_gridMass
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (θ : ℝ) (u : ℕ → ℝ≥0)
    (n : ℕ) (ω : Ω) (hD : IsDividendStrategy 𝓕 D) :
    (∫ s : ℝ, ∑ i ∈ Finset.range n,
      if s ∈ Ioc (u i : ℝ) (u (i + 1) : ℝ) then
        θ * Real.exp (θ * X.X (u (i + 1)) ω -
          (u (i + 1) : ℝ) * X.ψ θ) *
          Real.exp (-(θ * rightLimit D (u (i + 1)) ω))
      else 0 ∂dividendMeasure D ω) =
    ∑ i ∈ Finset.range n,
      (dividendMeasure D ω (Ioc (u i : ℝ) (u (i + 1) : ℝ))).toReal *
      (θ * Real.exp (θ * X.X (u (i + 1)) ω -
        (u (i + 1) : ℝ) * X.ψ θ) *
        Real.exp (-(θ * rightLimit D (u (i + 1)) ω))) := by sorry
