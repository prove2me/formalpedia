-- Prove2me | Theorems.Thm_DiscreteExpectation_rsIntegrable_identity_step
-- name    : DiscreteExpectation.rsIntegrable_identity_step
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:54:41.202667+00:00
-- url     : https://prove2.me/theorems/8354a253-56bc-42e9-872b-3180c64714f1
-- title:
--   Source theorem: DiscreteExpectation.rsIntegrable_identity_step
-- statement:
--   Source theorem extracted from ProbabilityTheory.chapter_01.def_1_3, with its proposition and original proof recorded separately.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/def_1_3.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_3_F003
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

theorem rsIntegrable_identity_step {c a b : ℝ} (ha : a < c) (hb : c < b) :
    RSIntegrable (fun x => x) (stepIndicator c) a b := by
  sorry
end DiscreteExpectation
end DiscreteExpectation
