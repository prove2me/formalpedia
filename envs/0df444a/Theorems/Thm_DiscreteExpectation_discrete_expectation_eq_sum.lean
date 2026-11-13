-- Prove2me | Theorems.Thm_DiscreteExpectation_discrete_expectation_eq_sum
-- name    : DiscreteExpectation.discrete_expectation_eq_sum
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T22:15:03.631376+00:00
-- url     : https://prove2.me/theorems/29314b73-2b44-48d3-930e-35ec5cc4da49
-- title:
--   Chapter 1, def_1_3: DiscreteExpectation.discrete_expectation_eq_sum
-- statement:
--   Source theorem `DiscreteExpectation.discrete_expectation_eq_sum` from Chapter 1, module `def_1_3`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/def_1_3.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_3_F000
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_3_F001
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_3_F003
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

noncomputable section

end   

noncomputable section DiscreteExpectation

namespace DiscreteExpectation

theorem discrete_expectation_eq_sum (m : ℕ) (c p : Fin m → ℝ)
    (a b : ℝ) (hab : a < b)
    (hp : ∀ i, 0 ≤ p i)
    (ha : ∀ i, a < c i)
    (hb : ∀ i, c i < b)
    (h_int : RSIntegrable (fun x => x) (discreteCDF m c p) a b) :
    cdfExpectation a b (discreteCDF m c p) h_int = ∑ i : Fin m, c i * p i := by sorry

end DiscreteExpectation   
end DiscreteExpectation   

section ContinuousExpectation

namespace ContinuousExpectation

end ContinuousExpectation   
end ContinuousExpectation
