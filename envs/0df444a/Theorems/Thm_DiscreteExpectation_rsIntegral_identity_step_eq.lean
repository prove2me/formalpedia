-- Prove2me | Theorems.Thm_DiscreteExpectation_rsIntegral_identity_step_eq
-- name    : DiscreteExpectation.rsIntegral_identity_step_eq
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:55:02.83556+00:00
-- url     : https://prove2.me/theorems/b8e6cdd6-2ef7-45f7-add8-c05a6fba82b8
-- title:
--   Source theorem: DiscreteExpectation.rsIntegral_identity_step_eq
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

theorem rsIntegral_identity_step_eq {c a b : ℝ} (ha : a < c) (hb : c < b)
    (h : RSIntegrable (fun x => x) (stepIndicator c) a b) :
    rsIntegral (fun x => x) (stepIndicator c) a b h = c := by
  sorry
end DiscreteExpectation
end DiscreteExpectation
