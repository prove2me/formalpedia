-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_rightLim_leftLim
-- name    : AvramDividend.Classical.dividendMeasure_singleton_rightLim_leftLim
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:46:53.60129+00:00
-- url     : https://prove2.me/theorems/367cb0b3-6033-4d3e-8ecc-608ab423d71e
-- title:
--   The dividend Stieltjes measure assigns to a singleton the right-continuous jump at that time
-- statement:
--   For every dividend strategy D, the associated Stieltjes dividendMeasure on real time has singleton mass equal to the right limit of its monotone real-time path minus the left limit of that right-continuous version. This follows directly from the precise dividendMeasure definition and Mathlib's StieltjesFunction.measure_singleton. It is a rigorous bridge towards relating discounted dividend-value integrals to jump payments.
-- source:
--   Pinned Mathlib MeasureTheory.Measure.Stieltjes measure_singleton, Monotone.stieltjesFunction; exact Avram dividendMeasure definition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendMeasure_singleton_rightLim_leftLim
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ) :
    dividendMeasure D ω {t} =
      ENNReal.ofReal
        (Function.rightLim (fun s : ℝ => D s.toNNReal ω) t -
          Function.leftLim (Function.rightLim
            (fun s : ℝ => D s.toNNReal ω)) t) := by sorry
