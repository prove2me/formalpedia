-- Prove2me | solution 1 for crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_of_nested
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:49:18.701216+00:00
-- url     : https://prove2.me/submissions/ff76d222-1f89-420b-86de-04552e24a037

import Definitions.Def_Operator_Crouzeix_ScalarCauchyKernelConstancy
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_ResolventCauchyKernel
import Theorems.Thm_contourIntegral_smul_const
import Theorems.Thm_normalized_contourIntegral_inv_sub_smul_resolvent_eq_resolvent
import Theorems.Thm_contourIntegral_contourIntegral_swap
import Theorems.Thm_integrableOn_nested_scalarCompanion_resolvent_kernel
import Theorems.Thm_contourIntegral_smul
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_eq
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange


section
open Complex Set spectrum
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
private theorem crouzeixAuxiliaryOperator_scalarCompanion_of_separated_integrable
    (A : E →L[ℂ] E) (Omega Psi : SmoothJordanDomain)
    (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hmass : contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E))
    (hsep : ∀ t : ℝ,
      Psi.boundaryParam t ∉ closure Omega.carrier)
    (hint : MeasureTheory.IntegrableOn (fun x : ℝ × ℝ =>
      deriv Omega.boundaryParam x.1 •
        (deriv Psi.boundaryParam x.2 •
          (star (Polynomial.eval (Psi.boundaryParam x.2) p) •
            ((2 * (Real.pi : ℂ) * I)⁻¹ •
              ((Psi.boundaryParam x.2 - Omega.boundaryParam x.1)⁻¹ •
                resolvent A (Omega.boundaryParam x.1))))))
      (uIoc (0 : ℝ) (2 * Real.pi) ×ˢ
        uIoc (0 : ℝ) (2 * Real.pi))) :
    crouzeixAuxiliaryOperator A Omega
        (crouzeixPolynomialScalarCompanion Psi p) =
      crouzeixPolynomialAuxiliaryOperator A Psi p := by
  let c : ℂ := (2 * (Real.pi : ℂ) * I)⁻¹
  let f : ℂ → ℂ → (E →L[ℂ] E) := fun z sigma =>
    star (Polynomial.eval sigma p) •
      (c • ((sigma - z)⁻¹ • resolvent A z))
  have hleft : ∀ z : ℂ,
      contourIntegral (f z) Psi.boundaryParam =
        crouzeixPolynomialScalarCompanion Psi p z • resolvent A z := by
    intro z
    have hfun : f z = fun sigma =>
        (c * (star (Polynomial.eval sigma p) * (sigma - z)⁻¹)) •
          resolvent A z := by
      funext sigma
      dsimp only [f]
      simp only [smul_smul]
      congr 1
      ring
    rw [hfun, contourIntegral_smul_const]
    have hscale := contourIntegral_smul c
      (fun sigma => star (Polynomial.eval sigma p) * (sigma - z)⁻¹)
      Psi.boundaryParam
    simp only [smul_eq_mul] at hscale
    rw [hscale]
    rfl
  have hright : ∀ (sigma : ℂ), sigma ∉ closure Omega.carrier →
      contourIntegral (fun z => f z sigma) Omega.boundaryParam =
        star (Polynomial.eval sigma p) • resolvent A sigma := by
    intro sigma hsigma
    dsimp only [f, c]
    rw [contourIntegral_smul, contourIntegral_smul,
      normalized_contourIntegral_inv_sub_smul_resolvent_eq_resolvent
        A Omega sigma hOmega hmass hsigma]
  unfold crouzeixPolynomialAuxiliaryOperator crouzeixAuxiliaryOperator
  congr 1
  calc
    contourIntegral
        (fun z => crouzeixPolynomialScalarCompanion Psi p z • resolvent A z)
        Omega.boundaryParam =
      contourIntegral (fun z => contourIntegral (f z) Psi.boundaryParam)
        Omega.boundaryParam := by
      congr 1
      funext z
      exact (hleft z).symm
    _ = contourIntegral
        (fun sigma => contourIntegral (fun z => f z sigma) Omega.boundaryParam)
        Psi.boundaryParam := by
      apply contourIntegral_contourIntegral_swap
      simpa only [f, c] using hint
    _ = contourIntegral
        (fun sigma => star (Polynomial.eval sigma p) • resolvent A sigma)
        Psi.boundaryParam := by
      unfold contourIntegral
      apply intervalIntegral.integral_congr
      intro t _ht
      change deriv Psi.boundaryParam t •
          contourIntegral (fun z => f z (Psi.boundaryParam t))
            Omega.boundaryParam =
        deriv Psi.boundaryParam t •
          (star (Polynomial.eval (Psi.boundaryParam t) p) •
            resolvent A (Psi.boundaryParam t))
      rw [hright (Psi.boundaryParam t) (hsep t)]
end

set_option autoImplicit false
open Complex Set spectrum
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega Psi : SmoothJordanDomain)
    (p : Polynomial ℂ)
    (hOmega : closure (numericalRange A) ⊆ Omega.carrier)
    (hmass : contourIntegral (resolvent A) Omega.boundaryParam =
      (2 * (Real.pi : ℂ) * I) • (1 : E →L[ℂ] E))
    (hnest : closure Omega.carrier ⊆ Psi.carrier) :
    crouzeixAuxiliaryOperator A Omega
        (crouzeixPolynomialScalarCompanionClosedExtension Psi p) =
      crouzeixPolynomialAuxiliaryOperator A Psi p := by
  have hsep : ∀ t : ℝ,
      Psi.boundaryParam t ∉ closure Omega.carrier := by
    intro t ht
    have hfrontier : Psi.boundaryParam t ∈ frontier Psi.carrier := by
      rw [← Psi.boundaryParam_range]
      exact mem_range_self t
    have hempty : Psi.boundaryParam t ∈ (∅ : Set ℂ) := by
      rw [← Psi.isOpen_carrier.inter_frontier_eq]
      exact ⟨hnest ht, hfrontier⟩
    exact hempty
  calc
    crouzeixAuxiliaryOperator A Omega
        (crouzeixPolynomialScalarCompanionClosedExtension Psi p) =
      crouzeixAuxiliaryOperator A Omega
        (crouzeixPolynomialScalarCompanion Psi p) := by
      unfold crouzeixAuxiliaryOperator
      congr 1
      unfold contourIntegral
      apply intervalIntegral.integral_congr
      intro t _ht
      have hfrontier : Omega.boundaryParam t ∈ frontier Omega.carrier := by
        rw [← Omega.boundaryParam_range]
        exact mem_range_self t
      change deriv Omega.boundaryParam t •
          (crouzeixPolynomialScalarCompanionClosedExtension Psi p
              (Omega.boundaryParam t) •
            resolvent A (Omega.boundaryParam t)) =
        deriv Omega.boundaryParam t •
          (crouzeixPolynomialScalarCompanion Psi p
              (Omega.boundaryParam t) •
            resolvent A (Omega.boundaryParam t))
      rw [crouzeixPolynomialScalarCompanionClosedExtension_eq Psi p
        (hnest (frontier_subset_closure hfrontier))]
    _ = crouzeixPolynomialAuxiliaryOperator A Psi p :=
      crouzeixAuxiliaryOperator_scalarCompanion_of_separated_integrable
        A Omega Psi p hOmega hmass hsep
          (integrableOn_nested_scalarCompanion_resolvent_kernel
            A Omega Psi p hOmega hnest)
