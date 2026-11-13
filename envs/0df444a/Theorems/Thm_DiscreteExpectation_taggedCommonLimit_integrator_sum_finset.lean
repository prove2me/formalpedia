-- Prove2me | Theorems.Thm_DiscreteExpectation_taggedCommonLimit_integrator_sum_finset
-- name    : DiscreteExpectation.taggedCommonLimit_integrator_sum_finset
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T21:59:16.696019+00:00
-- url     : https://prove2.me/theorems/82b1e800-aa67-4998-9e93-39da25f7d974
-- title:
--   ProbabilityTheory_chapter_01_def_1_3_F001: DiscreteExpectation.taggedCommonLimit_integrator_sum_finset
-- statement:
--   Source theorem `DiscreteExpectation.taggedCommonLimit_integrator_sum_finset` extracted from `ProbabilityTheory.chapter_01.def_1_3`. The formal Lean declaration specifies the proposition.
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

theorem taggedCommonLimit_integrator_sum_finset {m : ℕ} (s : Finset (Fin m))
    (α : Fin m → ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (h : ∀ i, RSIntegrable (fun x => x) (α i) a b) :
    TaggedCommonLimit a b (fun x => x) (fun x => ∑ i ∈ s, α i x)
      (∑ i ∈ s, rsIntegral (fun x => x) (α i) a b (h i)) := by
  sorry
end DiscreteExpectation
end DiscreteExpectation
