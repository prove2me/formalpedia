-- Prove2me | solution 1 for norm_crouzeixPolynomialScalarCompanion_le_infDist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:42:43.34428+00:00
-- url     : https://prove2.me/submissions/0820ef19-55a1-4786-bb3a-e2f72a7e8a66

import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Theorems.Thm_norm_crouzeixPolynomialScalarCompanion_le_of_boundary_separation
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Filter Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {z : ℂ} {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hC : ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
      ‖deriv Omega.boundaryParam t *
        star (Polynomial.eval (Omega.boundaryParam t) p)‖ ≤ C)
    (hz : z ∉ frontier Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanion Omega p z‖ ≤
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
        (2 * Real.pi *
          (C * (Metric.infDist z (frontier Omega.carrier))⁻¹)) := by
  have hfrontier : Omega.boundaryParam 0 ∈ frontier Omega.carrier := by
    rw [← Omega.boundaryParam_range]
    exact mem_range_self 0
  have hnonempty : (frontier Omega.carrier).Nonempty := ⟨_, hfrontier⟩
  have hdist_pos : 0 < Metric.infDist z (frontier Omega.carrier) :=
    (isClosed_frontier.notMem_iff_infDist_pos hnonempty).mp hz
  apply norm_crouzeixPolynomialScalarCompanion_le_of_boundary_separation
    Omega p hdist_pos hC_nonneg hC
  intro t ht
  have htfrontier : Omega.boundaryParam t ∈ frontier Omega.carrier := by
    rw [← Omega.boundaryParam_range]
    exact mem_range_self t
  simpa only [dist_eq_norm, norm_sub_rev] using
    (Metric.infDist_le_dist_of_mem htfrontier :
      Metric.infDist z (frontier Omega.carrier) ≤
        dist z (Omega.boundaryParam t))
