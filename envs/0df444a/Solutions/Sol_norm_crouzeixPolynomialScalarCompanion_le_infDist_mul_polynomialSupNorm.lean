-- Prove2me | solution 1 for norm_crouzeixPolynomialScalarCompanion_le_infDist_mul_polynomialSupNorm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:43:47.348194+00:00
-- url     : https://prove2.me/submissions/9f307270-6faf-45e3-ad17-130fa402b1d4

import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Theorems.Thm_norm_crouzeixPolynomialScalarCompanion_le_infDist
import Theorems.Thm_norm_eval_boundaryParam_le_polynomialSupNorm_frontier
import Theorems.Thm_polynomialSupNorm_nonneg


set_option autoImplicit false
open Complex Filter Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {z : ℂ} {D : ℝ}
    (hD_nonneg : 0 ≤ D)
    (hD : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t‖ ≤ D)
    (hz : z ∉ frontier Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanion Omega p z‖ ≤
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
        (2 * Real.pi *
          ((D * polynomialSupNorm p (frontier Omega.carrier)) *
            (Metric.infDist z (frontier Omega.carrier))⁻¹)) := by
  apply norm_crouzeixPolynomialScalarCompanion_le_infDist Omega p
    (mul_nonneg hD_nonneg (polynomialSupNorm_nonneg p _))
  · intro t ht
    rw [norm_mul, norm_star]
    exact mul_le_mul (hD t ht)
      (norm_eval_boundaryParam_le_polynomialSupNorm_frontier Omega p t)
      (norm_nonneg _) hD_nonneg
  · exact hz
