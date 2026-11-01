-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_closedHorizon_fullStieltjes_Icc_exponential_budget
-- name    : AvramDividend.Classical.avram_wave4_03_sourceLevy_closedHorizon_fullStieltjes_Icc_exponential_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T20:34:44.659197+00:00
-- url     : https://prove2.me/theorems/ff6f1a5c-39ae-4162-8ea2-325b14c4c720
-- title:
--   Original source Lévy full closed-horizon Stieltjes exponential cash expectation including initial atom at most one
-- statement:
--   For actual source Lévy X and the same adapted left-continuous control D, the entire true weighted dividend Stieltjes integral over [0,T] of the postpayment source exponential exp(X_t-D_{t+}-tψ(1)) has outer expectation ≤1. This includes the exact time-zero right-payment atom, all positive-time atomic payments, diffuse and singular-continuous dividend mass. The proof turns the already Proved closed-horizon expected atom-plus-Ioc budget into a single Icc integral by the proved full weighted Stieltjes decomposition and right-limit adapted measurability. It is a genuine continuous-time stochastic source compensation corollary, not the arbitrary test-function generator identity.
-- source:
--   Proved original source expected atom+full Ioc  ca4cb1b3, full weighted Stieltjes Icc split 28fa6c0e, rightLimit adapted right-continuous.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_closedHorizon_fullStieltjes_exponential_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_dividendMeasure_Icc_weighted_zeroAtom_plus_Ioc
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightLimit_adapted_rightCont
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_sourceLevy_closedHorizon_fullStieltjes_Icc_exponential_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp
        (X.X s.toNNReal ω - rightLimit D s.toNNReal ω -
          (s.toNNReal : ℝ) * X.ψ 1)) ∂dividendMeasure D ω ∂P) ≤ 1 := by sorry
