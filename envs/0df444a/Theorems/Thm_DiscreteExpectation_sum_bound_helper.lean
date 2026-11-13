-- Prove2me | Theorems.Thm_DiscreteExpectation_sum_bound_helper
-- name    : DiscreteExpectation.sum_bound_helper
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T22:14:15.979813+00:00
-- url     : https://prove2.me/theorems/3410fcce-b6d3-4f16-a682-7cacf52f2a11
-- title:
--   Chapter 1, def_1_3: DiscreteExpectation.sum_bound_helper
-- statement:
--   Source theorem `DiscreteExpectation.sum_bound_helper` from Chapter 1, module `def_1_3`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/def_1_3.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_3_F001
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_3_F002
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

noncomputable section

end   

noncomputable section DiscreteExpectation

namespace DiscreteExpectation

variable {a b : ℝ}

theorem sum_bound_helper (P : Partition a b) (c : ℝ) (ha : a < c) (hb : c < b)
    (vals : Fin P.n → ℝ) (hvals : ∀ i, vals i ∈ Partition.subinterval P i) :
    |∑ i : Fin P.n, vals i * (stepIndicator c (P.pts i.succ) - stepIndicator c (P.pts i.castSucc)) - c| ≤ P.mesh := by sorry

end DiscreteExpectation   
end DiscreteExpectation   

section ContinuousExpectation

namespace ContinuousExpectation

end ContinuousExpectation   
end ContinuousExpectation
