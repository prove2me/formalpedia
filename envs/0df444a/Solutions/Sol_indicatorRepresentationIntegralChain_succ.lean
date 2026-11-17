-- Prove2me | solution 1 for indicatorRepresentationIntegralChain_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:39:51.593901+00:00
-- url     : https://prove2.me/submissions/59c97efe-c5a6-40a4-8d08-8f7d3e351bd7

import Theorems.Thm_indicatorRepresentationIntegral_succ
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
    indicatorRepresentationIntegralChain (Ω := Ω) μ (n + 1) b B =
      match indicatorRepresentationIntegralChain (Ω := Ω) μ n (fun i => b i.succ) (fun i => B i.succ) with
      | some _ =>
          simpleFunctionIntegralAdd μ
            (indicatorRepresentationSummand (Ω := Ω) (n + 1) b B 0)
            (indicatorRepresentationSimpleFunction (Ω := Ω) n (fun i => b i.succ) (fun i => B i.succ))
      | none => none := by
  dsimp [indicatorRepresentationIntegralChain]
  cases htail :
      indicatorRepresentationIntegral (Ω := Ω) μ n
        (fun i => b i.succ) (fun i => B i.succ) with
  | none =>
      simpa [indicatorRepresentationIntegral_succ, htail]
  | some y =>
      simpa [indicatorRepresentationIntegral_succ, htail]
