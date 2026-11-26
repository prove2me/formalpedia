-- Prove2me | solution 1 for tendsto_crouzeixPolynomialScalarCompanionRegularized_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:46:15.824896+00:00
-- url     : https://prove2.me/submissions/b60c3b40-f54d-4072-91ad-0d8204085d82

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljCircle
import Theorems.Thm_crouzeixScalarCauchyKernel_ball_eq_one
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_ball_boundary_eq
import Theorems.Thm_crouzeixPolynomialScalarCompanion_ball_eq_eval_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_eq_regularized_add


set_option autoImplicit false
open Complex ComplexConjugate Filter Polynomial Set
open scoped Interval Real
theorem _root_.solution
    {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {xi : ℂ}
    (hxi : xi ∈ Metric.sphere (0 : ℂ) R) :
    Tendsto
      (crouzeixPolynomialScalarCompanionRegularized
        (SmoothJordanDomain.ball 0 R hR) p xi)
      (nhdsWithin xi (Metric.ball (0 : ℂ) R))
      (nhds
        (crouzeixPolynomialScalarCompanionRegularized
          (SmoothJordanDomain.ball 0 R hR) p xi xi)) := by
  have hboundary :=
    crouzeixPolynomialScalarCompanionRegularized_ball_boundary_eq hR p hxi
  have heq :
      crouzeixPolynomialScalarCompanionRegularized
          (SmoothJordanDomain.ball 0 R hR) p xi =ᶠ[
            nhdsWithin xi (Metric.ball (0 : ℂ) R)]
        fun _ ↦ star (Polynomial.eval 0 p) - star (Polynomial.eval xi p) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hzfrontier : z ∉ frontier
        (SmoothJordanDomain.ball 0 R hR).carrier := by
      intro hfrontier
      have hempty : z ∈ (∅ : Set ℂ) := by
        rw [← (SmoothJordanDomain.ball 0 R hR).isOpen_carrier.inter_frontier_eq]
        exact ⟨hz, hfrontier⟩
      exact hempty
    have hdecomp := crouzeixPolynomialScalarCompanion_eq_regularized_add
      (SmoothJordanDomain.ball 0 R hR) p xi
      hzfrontier
    rw [crouzeixPolynomialScalarCompanion_ball_eq_eval_zero hR p hz,
      crouzeixScalarCauchyKernel_ball_eq_one hR hz, mul_one] at hdecomp
    rw [hdecomp]
    ring
  rw [hboundary]
  exact tendsto_const_nhds.congr' heq.symm
