-- Prove2me | Theorems.Thm_DiscreteExpectation_rsIntegrable_integrator_sum_finset
-- name    : DiscreteExpectation.rsIntegrable_integrator_sum_finset
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T21:58:39.797587+00:00
-- url     : https://prove2.me/theorems/256cda19-8432-44da-9070-f10cac4e2a00
-- title:
--   ProbabilityTheory_chapter_01_def_1_3_F001: DiscreteExpectation.rsIntegrable_integrator_sum_finset
-- statement:
--   Source theorem `DiscreteExpectation.rsIntegrable_integrator_sum_finset` extracted from `ProbabilityTheory.chapter_01.def_1_3`. The formal Lean declaration specifies the proposition.
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

theorem rsIntegrable_integrator_sum_finset {m : ℕ} (s : Finset (Fin m))
    (α : Fin m → ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (h : ∀ i, RSIntegrable (fun x => x) (α i) a b) :  
    RSIntegrable (fun x => x) (fun x => ∑ i ∈ s, α i x) a b := by
  sorry
end DiscreteExpectation
end DiscreteExpectation
