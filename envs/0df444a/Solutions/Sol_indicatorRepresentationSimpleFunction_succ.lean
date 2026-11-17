-- Prove2me | solution 1 for indicatorRepresentationSimpleFunction_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:33:41.779856+00:00
-- url     : https://prove2.me/submissions/55ead775-9f7d-4815-8310-f1c920150df7

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

theorem solution
    (n : ℕ) (b : Fin (n + 1) → EReal) (B : Fin (n + 1) → Set Ω) :
    indicatorRepresentationSimpleFunction (Ω := Ω) (n + 1) b B =
      indicatorRepresentationSummand (Ω := Ω) (n + 1) b B 0 +
        indicatorRepresentationSimpleFunction (Ω := Ω) n (fun i => b i.succ) (fun i => B i.succ) := by
  simp [indicatorRepresentationSimpleFunction, indicatorRepresentationSummand, Fin.sum_univ_succ]
