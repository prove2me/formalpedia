-- Prove2me | solution 1 for intervalIntegrable_eval_smul_circleKernel_add_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:32:02.497743+00:00
-- url     : https://prove2.me/submissions/14f4f724-5036-4779-b220-f8e627790bba

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
    (hρ : Metric.sphere c R ⊆ resolventSet ℂ A) (hR : 0 ≤ R) (p : ℂ[X]) :
    IntervalIntegrable (fun t : ℝ => p.eval (circleMap c R t) •
      ((-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t) +
        ContinuousLinearMap.adjoint ((-I * deriv (circleMap c R) t) • resolvent A (circleMap c R t))))
      MeasureTheory.volume 0 (2 * Real.pi) :=
  ((p.continuous.comp (continuous_circleMap c R)).smul
    (continuous_circleKernel_add_adjoint A hρ hR)).intervalIntegrable 0 (2 * Real.pi)
