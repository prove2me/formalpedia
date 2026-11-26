-- Prove2me | solution 1 for resolvent_mul_aeval_eq_eval_mul_resolvent_sub_aeval_divByMonic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:30:35.538279+00:00
-- url     : https://prove2.me/submissions/e21398b8-c4ba-46d3-9757-6e79112d3b63

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_SpectralSet_Basic
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Polynomial
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
theorem _root_.solution
    (A : E →L[ℂ] E) (p : Polynomial ℂ) {z : ℂ} (hz : z ∈ resolventSet ℂ A) :
    resolvent A z * Polynomial.aeval A p =
      Polynomial.eval z p • resolvent A z -
        Polynomial.aeval A (p /ₘ (Polynomial.X - Polynomial.C z)) := by
  let q := p /ₘ (Polynomial.X - Polynomial.C z)
  have hpoly : Polynomial.C (Polynomial.eval z p) +
      (Polynomial.X - Polynomial.C z) * q = p := by
    rw [← Polynomial.modByMonic_X_sub_C_eq_C_eval p z]
    exact Polynomial.modByMonic_add_div p (Polynomial.X - Polynomial.C z)
  have hres : resolvent A z * (algebraMap ℂ (E →L[ℂ] E) z - A) = 1 := by
    calc
      resolvent A z * (algebraMap ℂ (E →L[ℂ] E) z - A) =
          (↑hz.unit⁻¹ : E →L[ℂ] E) * ↑hz.unit := by
        rw [spectrum.resolvent_eq hz, hz.unit_spec]
      _ = 1 := Units.inv_mul _
  conv_lhs => rhs; rw [← hpoly]
  simp only [map_add, map_mul, map_sub, Polynomial.aeval_C, Polynomial.aeval_X, mul_add,
    ← mul_assoc]
  rw [show A - algebraMap ℂ (E →L[ℂ] E) z =
      -(algebraMap ℂ (E →L[ℂ] E) z - A) by abel]
  rw [mul_neg, hres, neg_mul, one_mul]
  simp only [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, q, sub_eq_add_neg]
