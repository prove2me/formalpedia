-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_original_single_bounded_clock_budget_exact_transfer
-- name    : AvramDividend.Classical.avram_wave6_original_single_bounded_clock_budget_exact_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T18:12:26.607196+00:00
-- url     : https://prove2.me/theorems/8cbf957d-4747-434d-b852-29f2bba18ff9
-- title:
--   Original finite-horizon full discounted dividend bound from one sufficiently long bounded ruin-clock budget
-- statement:
--   For the actual source SpectrallyNegativeLevy P 𝓕 with admissible strategy D, a single expected full discounted dividendMeasure Stieltjes budget at the bounded stopped ruin clock min(ruinTime,a), where a exceeds the actual finite horizon T, transfers exactly to the full ruinTime payment domain. It is pathwise set equality rather than a Fatou or stochastic domination argument, and includes zero/infinite ruin and payment time zero. The stopped expected full Stieltjes budget remains an explicit hypothesis; no dividend Stieltjes decomposition or controlled Itô–Meyer is asserted.
-- source:
--   Original paymentTimes definition; new pathwise finite horizon payment domain clip theorem publication request 070f8c80-aa2d-42c9-be07-f5ccc20ae8ca; corrected core 429e17ca-5528-40b5-b593-7c03973d0706.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave6_original_single_bounded_clock_budget_exact_transfer
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (w : ℝ → ℝ)
    (T : ℝ) (hT : 0 ≤ T)
    (a : ℝ≥0∞) (hTa : ENNReal.ofReal T < a)
    (hBudget :
      (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) a) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x)) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
