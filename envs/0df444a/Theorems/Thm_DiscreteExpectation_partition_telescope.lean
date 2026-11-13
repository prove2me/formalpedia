-- Prove2me | Theorems.Thm_DiscreteExpectation_partition_telescope
-- name    : DiscreteExpectation.partition_telescope
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T22:13:58.136938+00:00
-- url     : https://prove2.me/theorems/8e283d65-96bd-418d-a02d-15af6a5d2537
-- title:
--   Chapter 1, def_1_3: DiscreteExpectation.partition_telescope
-- statement:
--   Source theorem `DiscreteExpectation.partition_telescope` from Chapter 1, module `def_1_3`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/def_1_3.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_3_F001
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

noncomputable section

end   

noncomputable section DiscreteExpectation

namespace DiscreteExpectation

theorem partition_telescope {a b : ℝ} (P : Partition a b) (F : ℝ → ℝ) :
    ∑ i : Fin P.n, (F (P.pts i.succ) - F (P.pts i.castSucc)) = F b - F a := by sorry

end DiscreteExpectation   
end DiscreteExpectation   

section ContinuousExpectation

namespace ContinuousExpectation

end ContinuousExpectation   
end ContinuousExpectation
