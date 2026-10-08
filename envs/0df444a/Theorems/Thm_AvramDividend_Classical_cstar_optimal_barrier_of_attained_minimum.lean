-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_optimal_barrier_of_attained_minimum
-- name    : AvramDividend.Classical.cstar_optimal_barrier_of_attained_minimum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T17:52:06.838653+00:00
-- url     : https://prove2.me/theorems/f474866b-11ea-4eeb-8820-c7385cff09c1
-- title:
--   Best Avram dividend barrier from an attained positive derivative minimum without boundary-gap assumptions
-- statement:
--   For a canonical Avram scale function, if cstar is itself a positive global derivative minimiser, the derivative at cstar is positive, and the function is differentiable in the interior of [0,cstar], then cstar is finite and its barrier dominates every competing barrier for x in [0,cstar]. No independent assumption about the one-sided derivative at zero is needed: its EReal liminf is automatically at least the global derivative minimum, including infinite and finite boundary cases.
-- source:
--   Use the new global-derivative-lower-to-right-liminf lemma on the defining cstarSet minimality to deduce deriv W cstar ≤ derivZeroPlus W. Split the EReal +infinity denominator, and otherwise use the exact EReal.toReal_le_toReal bridge already used in the Proved cstar_optimal_barrier_of_right_deriv_gap. The accepted attained-positive-minimum comparison handles all barrier-value branches. Nonnegativity and interval continuity of W come from IsScaleFunction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem cstar_optimal_barrier_of_attained_minimum
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hattain : (cstar W).toReal ∈ cstarSet W)
    (hpositive : 0 < deriv W (cstar W).toReal)
    (hdiff : DifferentiableOn ℝ W
      (Set.Ioo 0 (cstar W).toReal)) :
    cstar W < ⊤ ∧
      ∀ x b : ℝ, 0 ≤ x → x ≤ (cstar W).toReal → 0 ≤ b →
        barrierValue W b x ≤ vcstar W x := by
  sorry

end AvramDividend.Classical
