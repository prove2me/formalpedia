-- Prove2me | solution 1 for indicatorRepresentationIntegral_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:37:26.610726+00:00
-- url     : https://prove2.me/submissions/d64efa94-16ea-497e-b058-5b69ffb0a143

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
    indicatorRepresentationIntegral (Ω := Ω) μ (n + 1) b B =
      match indicatorRepresentationIntegral (Ω := Ω) μ n (fun i => b i.succ) (fun i => B i.succ) with
      | some _ =>
          simpleFunctionIntegralAdd μ
            (indicatorRepresentationSummand (Ω := Ω) (n + 1) b B 0)
            (indicatorRepresentationSimpleFunction (Ω := Ω) n (fun i => b i.succ) (fun i => B i.succ))
      | none => none := by
  congr! 2
