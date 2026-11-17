-- Prove2me | solution 1 for indicatorRepresentationWeightedSum_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:51:52.669347+00:00
-- url     : https://prove2.me/submissions/bee083b0-ba9f-47d2-96e9-e3a2c57db625

import Theorems.Thm_textbookERealFinSum_succ
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F001
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F000
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped BigOperators
variable {Ω : Type*} [MeasurableSpace Ω]

theorem solution (μ : Measure Ω)
    (n : ℕ) (b : Fin (n + 1) → EReal) (B : Fin (n + 1) → Set Ω) :
    indicatorRepresentationWeightedSum (Ω := Ω) μ (n + 1) b B =
      textbookIntegralAdd
        (some (b 0 * (μ (B 0) : EReal)))
        (indicatorRepresentationWeightedSum (Ω := Ω) μ n (fun i => b i.succ) (fun i => B i.succ)) := by
  simp [indicatorRepresentationWeightedSum, textbookERealFinSum_succ]
