-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ico_zero_eq_dividendValue
-- name    : AvramDividend.Classical.dividendMeasure_Ico_zero_eq_dividendValue
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T08:14:06.95645+00:00
-- url     : https://prove2.me/theorems/56472398-9e4f-43ea-9dc2-772f94a501cf
-- title:
--   The actual dividend Stieltjes measure on [0,t) equals cumulative dividends D(t), including continuous payments
-- statement:
--   For every true dividend strategy D with D(0)=0, its Stieltjes dividendMeasure satisfies dividendMeasure D ω ([0,t)) = ENNReal.ofReal(D(t,ω)) for every nonnegative t, including continuous dividend accumulation and right-jump dividend payments. This follows from the generic monotone left-continuous Stieltjes half-open interval formula and left-continuity of the canonical real extension. It strengthens the previous singleton-only results and is a central deterministic ingredient in controlling the full dividend integral.
-- source:
--   Children monotone_leftcontinuous_stieltjes_measure_Ico and dividendStrategy_real_extension_leftContinuous, formal dividendMeasure and IsDividendStrategy definitions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendMeasure_Ico_zero_eq_dividendValue
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) :
    dividendMeasure D ω (Ico (0 : ℝ) (t : ℝ)) =
      ENNReal.ofReal (D t ω) := by sorry
