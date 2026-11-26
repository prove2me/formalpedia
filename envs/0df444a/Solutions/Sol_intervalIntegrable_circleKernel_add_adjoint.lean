-- Prove2me | solution 1 for intervalIntegrable_circleKernel_add_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:31:56.725804+00:00
-- url     : https://prove2.me/submissions/64ec7538-1dbe-4164-b04f-e323b9596ca9

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_Crouzeix_CircleKernel
import Theorems.Thm_continuous_circleKernel_add_adjoint

set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution (A : E →L[ℂ] E) {c : ℂ} {R : ℝ}
    (hρ : Metric.sphere c R ⊆ resolventSet ℂ A) (hR : 0 ≤ R) :
    IntervalIntegrable (fun t : ℝ =>
      (-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t) +
        ContinuousLinearMap.adjoint ((-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t)))
      MeasureTheory.volume 0 (2 * Real.pi) :=
  (continuous_circleKernel_add_adjoint A hρ hR).intervalIntegrable 0 (2 * Real.pi)
