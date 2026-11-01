-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_positiveTime_fullStieltjes_exponential_budget_q_ge_psi
-- name    : AvramDividend.Classical.avram_wave4_03_sourceLevy_positiveTime_fullStieltjes_exponential_budget_q_ge_psi
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T23:58:05.669405+00:00
-- url     : https://prove2.me/theorems/2f4db822-a39f-40b8-a179-0a0b60897920
-- title:
--   Original Lévy full-Stieltjes source exponential budget at every discount at least ψ(1)
-- statement:
--   On the genuine original Lévy probability space with an adapted left-continuous right-payment control D and its complete positive-time Stieltjes measure, any discount rate q at least ψ(1) gives expected source controlled exponential payment mass at most one. The result includes diffuse and singular-continuous dividends and all positive-time right-payment atoms. It derives by monotonicity of the discount from the Proved original-source martingale compensation identity, and makes no assertion about arbitrary C1 HJB test functions.
-- source:
--   Proved original-source full-Stieltjes exponential compensation budget 6e0c195d-1303-4a59-98cd-6418970065ab.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_positiveTime_fullStieltjes_exponential_budget
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.avram_wave4_03_sourceLevy_positiveTime_fullStieltjes_exponential_budget_q_ge_psi
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : X.ψ 1 ≤ q)
    (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ s : ℝ,
      if s ∈ Ioc (0 : ℝ) (T : ℝ) then
        ENNReal.ofReal (Real.exp
          (X.X s.toNNReal ω - rightLimit D s.toNNReal ω -
            (s.toNNReal : ℝ) * q))
      else 0 ∂dividendMeasure D ω ∂P) ≤ 1 := by sorry
