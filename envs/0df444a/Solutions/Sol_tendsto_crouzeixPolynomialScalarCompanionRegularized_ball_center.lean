-- Prove2me | solution 1 for tendsto_crouzeixPolynomialScalarCompanionRegularized_ball_center
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:45:24.673287+00:00
-- url     : https://prove2.me/submissions/ee34c1d7-f912-4755-8343-fffa6ed1cfd1

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljCircle
import Theorems.Thm_crouzeixScalarCauchyKernel_ball_center_eq_one
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_ball_center_boundary_eq
import Theorems.Thm_crouzeixPolynomialScalarCompanion_ball_center_eq_eval_center
import Theorems.Thm_crouzeixPolynomialScalarCompanion_eq_regularized_add


set_option autoImplicit false
open Complex ComplexConjugate Filter Polynomial Set
open scoped Interval Real
theorem _root_.solution
    (c : ℂ) {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {xi : ℂ}
    (hxi : xi ∈ Metric.sphere c R) :
    Tendsto
      (crouzeixPolynomialScalarCompanionRegularized
        (SmoothJordanDomain.ball c R hR) p xi)
      (nhdsWithin xi (Metric.ball c R))
      (nhds
        (crouzeixPolynomialScalarCompanionRegularized
          (SmoothJordanDomain.ball c R hR) p xi xi)) := by
  have hboundary :=
    crouzeixPolynomialScalarCompanionRegularized_ball_center_boundary_eq
      c hR p hxi
  have heq :
      crouzeixPolynomialScalarCompanionRegularized
          (SmoothJordanDomain.ball c R hR) p xi =ᶠ[
            nhdsWithin xi (Metric.ball c R)]
        fun _ ↦ star (Polynomial.eval c p) - star (Polynomial.eval xi p) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hzfrontier : z ∉ frontier
        (SmoothJordanDomain.ball c R hR).carrier := by
      intro hfrontier
      have hempty : z ∈ (∅ : Set ℂ) := by
        rw [← (SmoothJordanDomain.ball c R hR).isOpen_carrier.inter_frontier_eq]
        exact ⟨hz, hfrontier⟩
      exact hempty
    have hdecomp := crouzeixPolynomialScalarCompanion_eq_regularized_add
      (SmoothJordanDomain.ball c R hR) p xi hzfrontier
    rw [crouzeixPolynomialScalarCompanion_ball_center_eq_eval_center c hR p hz,
      crouzeixScalarCauchyKernel_ball_center_eq_one c hR hz, mul_one] at hdecomp
    rw [hdecomp]
    ring
  rw [hboundary]
  exact tendsto_const_nhds.congr' heq.symm
