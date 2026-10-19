-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_eq_stieltjes
-- name    : AvramDividend.Classical.runningSup_dividendMeasure_eq_stieltjes
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T11:24:37.284251+00:00
-- url     : https://prove2.me/theorems/036fcdf6-3be7-4bd6-a17a-92fb44710834
-- title:
--   Actual running supremum dividend measure is the genuine Lebesgue–Stieltjes measure
-- statement:
--   The dividendMeasure definition uses the Stieltjes measure when the real-time path t↦D(t.toNNReal) is monotone, and falls back to zero otherwise. For the actual Lévy running supremum S, monotonicity follows from its already remotely proved nondecreasing NNReal-time path and monotonicity of Real.toNNReal. Consequently dividendMeasure(S) is the genuine Lebesgue–Stieltjes measure h.stieltjesFunction.measure with the monotonicity witness h, never an unexplained zero fallback. This is an essential interface for translating stopped record-level sums into the actual dividend reward.
-- source:
--   Prove2Me proved runningSup_monotone_and_path_le 848fbd48-f69f-46b9-b2bf-436cb33918a8; dividendMeasure definition in Def_AvramDividend_Classical_DividendStrategy; Mathlib Real.toNNReal_mono at the pinned revision.

import Mathlib.Data.NNReal.Defs
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_dividendMeasure_eq_stieltjes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    ∃ h : Monotone (fun t : ℝ => runningSup X t.toNNReal ω),
      dividendMeasure (runningSup X) ω = h.stieltjesFunction.measure := by sorry
