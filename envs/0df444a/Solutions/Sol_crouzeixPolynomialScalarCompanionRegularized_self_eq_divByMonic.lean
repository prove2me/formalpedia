-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionRegularized_self_eq_divByMonic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:09:21.606054+00:00
-- url     : https://prove2.me/submissions/cbb67aa0-12ca-41d7-beaa-478fec2367a4

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi : ℂ) :
    crouzeixPolynomialScalarCompanionRegularized Omega p xi xi =
      (2 * (Real.pi : ℂ) * I)⁻¹ *
        contourIntegral
          (fun sigma ↦
            star (sigma - xi) *
              star (Polynomial.eval sigma
                (p /ₘ (Polynomial.X - Polynomial.C xi))) *
              (sigma - xi)⁻¹)
          Omega.boundaryParam := by
  let q := p /ₘ (Polynomial.X - Polynomial.C xi)
  have hpoly : Polynomial.C (Polynomial.eval xi p) +
      (Polynomial.X - Polynomial.C xi) * q = p := by
    rw [← Polynomial.modByMonic_X_sub_C_eq_C_eval p xi]
    exact Polynomial.modByMonic_add_div p (Polynomial.X - Polynomial.C xi)
  have heval : ∀ sigma : ℂ,
      Polynomial.eval sigma p - Polynomial.eval xi p =
        (sigma - xi) * Polynomial.eval sigma q := by
    intro sigma
    have h := congrArg (Polynomial.eval sigma) hpoly
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_X] at h
    rw [← h]
    ring
  unfold crouzeixPolynomialScalarCompanionRegularized
  congr 1
  unfold contourIntegral
  apply intervalIntegral.integral_congr
  intro t _
  change deriv Omega.boundaryParam t *
      ((star (Polynomial.eval (Omega.boundaryParam t) p) -
          star (Polynomial.eval xi p)) *
        (Omega.boundaryParam t - xi)⁻¹) =
    deriv Omega.boundaryParam t *
      (star (Omega.boundaryParam t - xi) *
        star (Polynomial.eval (Omega.boundaryParam t) q) *
          (Omega.boundaryParam t - xi)⁻¹)
  rw [← star_sub, heval, star_mul]
  ring
