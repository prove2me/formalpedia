-- Prove2me | solution 1 for crouzeixBoundaryPhaseContractive_of_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:49:00.900929+00:00
-- url     : https://prove2.me/submissions/4a90b4f6-c49e-4d5f-b612-3b7f056088f3

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Theorems.Thm_SmoothJordanDomain_frontier_infinite
import Theorems.Thm_crouzeixBoundaryPhaseContractive_smul
import Theorems.Thm_crouzeixBoundaryPhaseContractive_of_natDegree_eq_zero
import Theorems.Thm_SmoothJordanDomain_isCompact_frontier
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
theorem _root_.solution
    (Omega : SmoothJordanDomain)
    (hnormalized : ∀ p : Polynomial ℂ, 0 < p.natDegree →
      polynomialSupNorm p (frontier Omega.carrier) = 1 →
      CrouzeixBoundaryPhaseContractive Omega p) :
    ∀ p, CrouzeixBoundaryPhaseContractive Omega p := by
  intro p
  by_cases hpzero : p.natDegree = 0
  · exact crouzeixBoundaryPhaseContractive_of_natDegree_eq_zero
      Omega p hpzero
  have hp : 0 < p.natDegree := Nat.pos_of_ne_zero hpzero
  let m := polynomialSupNorm p (frontier Omega.carrier)
  have hm0 : m ≠ 0 := by
    intro hm
    have hpzero' : p = 0 :=
      polynomial_eq_zero_of_polynomialSupNorm_eq_zero p
        Omega.isCompact_frontier Omega.frontier_infinite hm
    subst p
    simp only [Polynomial.natDegree_zero, lt_self_iff_false] at hp
  have hm : 0 < m :=
    lt_of_le_of_ne (polynomialSupNorm_nonneg p _) (Ne.symm hm0)
  let q : Polynomial ℂ := ((m : ℂ)⁻¹) • p
  have hscalar : ((m : ℂ)⁻¹) ≠ 0 :=
    inv_ne_zero (Complex.ofReal_ne_zero.mpr hm0)
  have hqdegree : 0 < q.natDegree := by
    dsimp only [q]
    rw [Polynomial.natDegree_smul p hscalar]
    exact hp
  have hqnorm : polynomialSupNorm q (frontier Omega.carrier) = 1 := by
    dsimp only [q]
    rw [polynomialSupNorm_smul]
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm]
    exact inv_mul_cancel₀ hm0
  have hq := hnormalized q hqdegree hqnorm
  have hscaled := crouzeixBoundaryPhaseContractive_smul
    Omega (m : ℂ) q hq
  have hpq : (m : ℂ) • q = p := by
    dsimp only [q]
    rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hm0),
      one_smul]
  rw [hpq] at hscaled
  exact hscaled
