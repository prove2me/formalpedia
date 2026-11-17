-- Prove2me | solution 1 for sourceSupIntegral_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:14:21.605202+00:00
-- url     : https://prove2.me/submissions/6ac443b1-fbae-4494-a61a-5b3dbf615c6e

import Definitions.Def_ProbabilityTheory_chapter_06_thm_6_3_F000
import Theorems.Thm_sourceSimpleApproximationSet_mono
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

theorem solution (μ : Measure Ω) {X Y : Ω → ENNReal}
    (hsub : sourceSimpleApproximationSet X ⊆ sourceSimpleApproximationSet Y) :
    sourceSupIntegral μ X ≤ sourceSupIntegral μ Y := by
  unfold sourceSupIntegral
  refine iSup_le ?_
  intro f
  exact le_iSup
    (fun g : sourceSimpleApproximationSet Y =>
      sourceSimpleApproximationIntegral μ g.1)
    ⟨f.1, hsub f.2⟩
