-- Prove2me | solution 1 for eq_smul_resolvent_apply_sub_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:29:55.698252+00:00
-- url     : https://prove2.me/submissions/b8516032-0cc7-4271-8ed0-5ed4de73c558

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.InnerProductSpace.Positive
import Definitions.Def_Operator_NumericalRange_Helpers
import Definitions.Def_Operator_Crouzeix_DoubleLayer
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (A : E →L[ℂ] E) {σ : ℂ}
    (hσ : σ ∈ resolventSet ℂ A) (x : E) :
    x = σ • resolvent A σ x - A (resolvent A σ x) := by
  have hmul : (σ • (1 : E →L[ℂ] E) - A) * resolvent A σ = 1 := by
    have hunit : σ • (1 : E →L[ℂ] E) - A = (hσ.unit : E →L[ℂ] E) := by
      simpa only [Algebra.algebraMap_eq_smul_one] using hσ.unit_spec.symm
    calc
      (σ • (1 : E →L[ℂ] E) - A) * resolvent A σ =
          (hσ.unit : E →L[ℂ] E) * (↑((hσ.unit)⁻¹) : E →L[ℂ] E) := by
            rw [hunit, spectrum.resolvent_eq hσ]
      _ = 1 := Units.mul_inv _
  have h := congrArg (fun T : E →L[ℂ] E => T x) hmul
  simpa only [mul_apply_eq_comp, sub_apply, smul_apply, one_apply_eq_self] using h.symm
