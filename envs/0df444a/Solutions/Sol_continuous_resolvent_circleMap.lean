-- Prove2me | solution 1 for continuous_resolvent_circleMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:59:42.664807+00:00
-- url     : https://prove2.me/submissions/31a60ec6-4ae6-4833-8bb8-20d7ead5a409

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_Crouzeix_CircleKernel

set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution (A : E →L[ℂ] E) {c : ℂ} {R : ℝ}
    (hρ : Metric.sphere c R ⊆ resolventSet ℂ A) (hR : 0 ≤ R) :
    Continuous (fun t : ℝ => resolvent A (circleMap c R t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact ((spectrum.hasDerivAt_resolvent_const_left
    (hρ (circleMap_mem_sphere c hR t))).continuousAt).comp (continuous_circleMap c R).continuousAt
