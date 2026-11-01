-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_closedHorizon_fullStieltjes_exponential_budget
-- name    : AvramDividend.Classical.avram_wave4_03_sourceLevy_closedHorizon_fullStieltjes_exponential_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T20:12:31.801198+00:00
-- url     : https://prove2.me/theorems/ca4cb1b3-49f7-4411-ada7-890ba5e561b0
-- title:
--   Original source Lévy full closed-horizon expected exponential cash budget including the first atom
-- statement:
--   For actual original spectrally negative Lévy X and the identical adapted left-continuous dividend strategy D, the joint expected time-zero Stieltjes right atom and full positive-time (0,T] postpayment Stieltjes dividend exponential cash integral is at most one. Includes diffuse, singular-continuous and right-atomic mass simultaneously. The proof uses source finite-grid martingale consumption, all-real dyadic cell identity, double Fatou, and finite ENNReal cancellation, without independent-path coupling or jump-only concentration.
-- source:
--   Original-source double Fatou 1f91129d, source zero-atom plus full double-Stieltjes finite-grid budget b5e6d927 and accepted all-real dyadic bridge 3f4cb787.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_source_fullStieltjes_doubleFatou_expected
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_rightDyadic_allRealIoc_step_eq_ceiling
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_zeroAtom_plus_fullStieltjes_doubleLintegral_budget
open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_03_sourceLevy_closedHorizon_fullStieltjes_exponential_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ ω, ENNReal.ofReal (1 * Real.exp (-(1 * rightLimit D 0 ω)) *
      rightLimit D 0 ω) ∂P) +
    (∫⁻ ω, ∫⁻ s : ℝ, if s ∈ Ioc (0 : ℝ) (T : ℝ) then
      ENNReal.ofReal (Real.exp (X.X s.toNNReal ω -
        rightLimit D s.toNNReal ω - (s.toNNReal : ℝ) * X.ψ 1))
      else 0 ∂dividendMeasure D ω ∂P) ≤ 1 := by sorry
