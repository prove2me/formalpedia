-- Prove2me | solution 1 for sphere_subset_resolventSet_of_closure_numericalRange_subset_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:31:40.091812+00:00
-- url     : https://prove2.me/submissions/ba232088-50ed-4429-a6ac-a3dd0aebb548

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_Crouzeix_CircleKernel
import Theorems.Thm_spectrum_subset_closure_numericalRange


set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution (A : E →L[ℂ] E)
    {c : ℂ} {R : ℝ} (hW : closure (numericalRange A) ⊆ Metric.ball c R) :
    Metric.sphere c R ⊆ resolventSet ℂ A := by
  intro z hz
  rw [mem_resolventSet_iff, ← spectrum.notMem_iff]
  intro hzσ
  have hzb : z ∈ Metric.ball c R := hW (spectrum_subset_closure_numericalRange A hzσ)
  rw [Metric.mem_ball] at hzb
  rw [Metric.mem_sphere] at hz
  exact lt_irrefl _ (hz ▸ hzb)
