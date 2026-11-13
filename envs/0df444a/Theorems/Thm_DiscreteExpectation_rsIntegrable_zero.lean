-- Prove2me | Theorems.Thm_DiscreteExpectation_rsIntegrable_zero
-- name    : DiscreteExpectation.rsIntegrable_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T21:58:25.938065+00:00
-- url     : https://prove2.me/theorems/4836afa2-7118-4040-bca2-69d0bc717562
-- title:
--   ProbabilityTheory_chapter_01_def_1_3_F001: DiscreteExpectation.rsIntegrable_zero
-- statement:
--   Source theorem `DiscreteExpectation.rsIntegrable_zero` extracted from `ProbabilityTheory.chapter_01.def_1_3`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/def_1_3.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_3_F001
import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_3_F001
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic
noncomputable section
end
noncomputable section DiscreteExpectation
namespace DiscreteExpectation

theorem rsIntegrable_zero (a b : ℝ) (hab : a < b) :
    RSIntegrable (fun x => x) (fun _ => 0) a b := by
  sorry
end DiscreteExpectation
end DiscreteExpectation
