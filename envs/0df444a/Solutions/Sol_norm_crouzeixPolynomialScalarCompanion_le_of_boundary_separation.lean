-- Prove2me | solution 1 for norm_crouzeixPolynomialScalarCompanion_le_of_boundary_separation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:41:54.919903+00:00
-- url     : https://prove2.me/submissions/13a84af5-fc18-4c9e-b651-522b413cbc0f

import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_norm_contourIntegral_le_of_norm_le_const
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Filter Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {z : ℂ} {delta C : ℝ}
    (hdelta : 0 < delta) (hC_nonneg : 0 ≤ C)
    (hC : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t *
        star (Polynomial.eval (Omega.boundaryParam t) p)‖ ≤ C)
    (hsep : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      delta ≤ ‖Omega.boundaryParam t - z‖) :
    ‖crouzeixPolynomialScalarCompanion Omega p z‖ ≤
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
        (2 * Real.pi * (C * delta⁻¹)) := by
  have hintegrand : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t •
        (star (Polynomial.eval (Omega.boundaryParam t) p) *
          (Omega.boundaryParam t - z)⁻¹)‖ ≤ C * delta⁻¹ := by
    intro t ht
    have hdenpos : 0 < ‖Omega.boundaryParam t - z‖ :=
      hdelta.trans_le (hsep t ht)
    have hinv : ‖Omega.boundaryParam t - z‖⁻¹ ≤ delta⁻¹ :=
      (inv_le_inv₀ hdenpos hdelta).2 (hsep t ht)
    have hCt := hC t ht
    rw [norm_mul] at hCt
    simp only [smul_eq_mul, ← mul_assoc, norm_mul, norm_inv]
    exact mul_le_mul hCt hinv (inv_nonneg.mpr (norm_nonneg _)) hC_nonneg
  unfold crouzeixPolynomialScalarCompanion
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_contourIntegral_le_of_norm_le_const hintegrand) (norm_nonneg _)
