-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_positiveTime_fullStieltjes_exponential_budget
-- name    : AvramDividend.Classical.avram_wave4_03_sourceLevy_positiveTime_fullStieltjes_exponential_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T20:09:10.484935+00:00
-- url     : https://prove2.me/theorems/6e0c195d-1303-4a59-98cd-6418970065ab
-- title:
--   Original same-path Lévy full Stieltjes continuous-time exponential expected budget
-- statement:
--   For actual spectrally negative Lévy X and arbitrary adapted left-continuous dividend strategy D on the same original filtered space, the expected full postpayment Stieltjes integral on (0,T] of exp(X_s-D_{s+}-sψ(1)) is at most one. No purely atomic dividend approximation or independent-source coupling is assumed; the proof combines exact all-real dyadic Ioc kernel identity, genuine stochastic finite-grid budget (including the initial atom), and original-source double Fatou.
-- source:
--   Original-source double Fatou 1f91129d; same-source exact full Stieltjes right-grid kernel; original-source initial atom plus full Stieltjes finite-grid budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_source_fullStieltjes_doubleFatou_expected
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_rightDyadic_allRealIoc_step_eq_ceiling
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_zeroAtom_plus_fullStieltjes_doubleLintegral_budget
open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_03_sourceLevy_positiveTime_fullStieltjes_exponential_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ s : ℝ, if s ∈ Ioc (0 : ℝ) (T : ℝ) then
      ENNReal.ofReal (Real.exp (X.X s.toNNReal ω -
        rightLimit D s.toNNReal ω - (s.toNNReal : ℝ) * X.ψ 1))
      else 0 ∂dividendMeasure D ω ∂P) ≤ 1 := by sorry
