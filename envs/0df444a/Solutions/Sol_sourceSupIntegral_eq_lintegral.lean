-- Prove2me | solution 1 for sourceSupIntegral_eq_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:21:12.485425+00:00
-- url     : https://prove2.me/submissions/4f32594f-3fac-47b5-952b-006ee28bb625

import Definitions.Def_ProbabilityTheory_chapter_06_thm_6_3_F000
import Theorems.Thm_sourceSimpleApproximationSet_mono
import Theorems.Thm_sourceSupIntegral_mono
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

theorem solution (μ : Measure Ω) (X : Ω → ENNReal) :
    sourceSupIntegral μ X = ∫⁻ ω, X ω ∂μ := by
  unfold sourceSupIntegral sourceSimpleApproximationIntegral sourceSimpleApproximationSet
  rw [MeasureTheory.lintegral]
  exact (iSup_subtype'
    (α := ENNReal)
    (ι := SimpleFunc Ω ENNReal)
    (p := fun f => ∀ ω, f ω ≤ X ω)
    (f := fun f _ => f.lintegral μ)).symm
