-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_theta_scaled_closedHorizon_Icc_fullStieltjes_budget
-- name    : AvramDividend.Classical.avram_wave4_03_sourceLevy_theta_scaled_closedHorizon_Icc_fullStieltjes_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T00:30:33.481789+00:00
-- url     : https://prove2.me/theorems/9222270b-c31d-4338-b6f5-2966a32134f6
-- title:
--   Full original-source closed Stieltjes theta-exponential martingale budget including zero atom
-- statement:
--   For every positive theta, original adapted dividend strategy D, and finite positive horizon T, the expectation of theta times the compensated postpayment source exponential integrated against the entire Stieltjes dividend measure on [0,T] is at most one. The original initial atom, diffuse mass, singular-continuous component and right atoms are included. Derived from full source theta stochastic finite-grid budget and exact true Stieltjes Icc zero-atom split.
-- source:
--   Original source theta double-budget child (new) and exact full-Icc Stieltjes atom-accounting lemma 5ceaf5b7.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_theta_scaled_fullStieltjes_doubleBudget
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_dividendMeasure_Icc_weighted_zeroAtom_plus_Ioc
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_sourceLevy_theta_scaled_closedHorizon_Icc_fullStieltjes_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ : ℝ) (hθ : 0 < θ)
    (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (θ * Real.exp (θ *
        (X.X s.toNNReal ω - rightLimit D s.toNNReal ω) -
        (s.toNNReal : ℝ) * X.ψ θ))
        ∂dividendMeasure D ω ∂P) ≤ 1 := by sorry
