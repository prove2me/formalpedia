-- Prove2me | solution 1 for crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_of_normalized_vanishingAtZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:26:41.946384+00:00
-- url     : https://prove2.me/submissions/18577777-375d-418b-9502-9e9a2051e3ec

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Theorems.Thm_crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_smul_eq_iff
import Theorems.Thm_crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_eq_iff_sub_C_eval_zero
import Theorems.Thm_SmoothJordanDomain_frontier_infinite
import Theorems.Thm_SmoothJordanDomain_isCompact_frontier
import Theorems.Thm_crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_C_of_cauchyKernel_eq_one
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_polynomialSupNorm_nonneg
import Theorems.Thm_polynomialSupNorm_smul
import Theorems.Thm_polynomial_eq_zero_of_polynomialSupNorm_eq_zero
attribute [local simp] crouzeixPolynomialBoundaryPhaseTransform_zero
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    (hnormalized : ∀ p : Polynomial ℂ,
      0 < p.natDegree →
      Polynomial.eval 0 p = 0 →
      polynomialSupNorm p (frontier Omega.carrier) = 1 →
      crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega p) =
        crouzeixPolynomialAuxiliaryOperator A Omega p) :
    ∀ p : Polynomial ℂ,
      crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega p) =
        crouzeixPolynomialAuxiliaryOperator A Omega p := by
  intro p
  by_cases hpzero : p.natDegree = 0
  · rw [Polynomial.eq_C_of_natDegree_eq_zero hpzero]
    exact
      crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_C_of_cauchyKernel_eq_one
        A Omega (p.coeff 0) hkernel
  have hp : 0 < p.natDegree := Nat.pos_of_ne_zero hpzero
  let q := p - Polynomial.C (Polynomial.eval 0 p)
  have hqdegree : 0 < q.natDegree := by
    simpa only [q, Polynomial.natDegree_sub_C] using hp
  have hqeval : Polynomial.eval 0 q = 0 := by
    simp only [q, Polynomial.eval_sub, Polynomial.eval_C, sub_self]
  let m := polynomialSupNorm q (frontier Omega.carrier)
  have hm0 : m ≠ 0 := by
    intro hm
    have hqzero : q = 0 :=
      polynomial_eq_zero_of_polynomialSupNorm_eq_zero q
        Omega.isCompact_frontier Omega.frontier_infinite hm
    have hpC : p = Polynomial.C (Polynomial.eval 0 p) := by
      apply sub_eq_zero.mp
      simpa only [q] using hqzero
    apply hpzero
    rw [hpC, Polynomial.natDegree_C]
  have hm : 0 < m :=
    lt_of_le_of_ne (polynomialSupNorm_nonneg q _) (Ne.symm hm0)
  let r : Polynomial ℂ := ((m : ℂ)⁻¹) • q
  have hrdegree : 0 < r.natDegree := by
    dsimp only [r]
    rw [Polynomial.natDegree_smul q
      (inv_ne_zero (Complex.ofReal_ne_zero.mpr hm0))]
    exact hqdegree
  have hreval : Polynomial.eval 0 r = 0 := by
    simp only [r, Polynomial.eval_smul, hqeval, smul_zero]
  have hrnorm : polynomialSupNorm r (frontier Omega.carrier) = 1 := by
    dsimp only [r]
    rw [polynomialSupNorm_smul]
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm]
    exact inv_mul_cancel₀ hm0
  have hr := hnormalized r hrdegree hreval hrnorm
  have hmcomplex : (m : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hm0
  have hmq : (m : ℂ) • r = q := by
    dsimp only [r]
    rw [smul_smul, mul_inv_cancel₀ hmcomplex, one_smul]
  have hq :
      crouzeixAuxiliaryOperator A Omega
          (crouzeixPolynomialScalarCompanionClosedExtension Omega q) =
        crouzeixPolynomialAuxiliaryOperator A Omega q := by
    have hscaled :=
      (crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_smul_eq_iff
        A Omega hmcomplex r hkernel).2 hr
    rwa [hmq] at hscaled
  exact
    (crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_eq_iff_sub_C_eval_zero
      A Omega p hOmega hkernel).2 hq
