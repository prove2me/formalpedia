-- Prove2me | solution 1 for exists_uniform_norm_inward_regularized_integrand_sub_le_deriv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:58:44.194139+00:00
-- url     : https://prove2.me/submissions/87311084-dca8-4c37-90e0-e8154660d0cf

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_exists_uniform_norm_eval_divByMonic_X_sub_C_frontier_le
import Theorems.Thm_exists_uniform_norm_inward_regularized_integrand_sub_le

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) {c : ℂ}
    (hc : c ∈ Omega.carrier) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ xi ∈ frontier Omega.carrier,
        ∀ r ∈ Ioc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) (2 * Real.pi),
          ‖deriv Omega.boundaryParam t •
            (((star (Polynomial.eval (Omega.boundaryParam t) p) -
                  star (Polynomial.eval xi p)) *
                (Omega.boundaryParam t -
                  smoothJordanInwardPoint c xi r)⁻¹) -
              ((star (Polynomial.eval (Omega.boundaryParam t) p) -
                  star (Polynomial.eval xi p)) *
                (Omega.boundaryParam t - xi)⁻¹))‖ ≤
            C * ‖deriv Omega.boundaryParam t‖ := by
  obtain ⟨C, hC, hdom⟩ :=
    exists_uniform_norm_inward_regularized_integrand_sub_le Omega p hc
  obtain ⟨Q, hQ, hq⟩ :=
    exists_uniform_norm_eval_divByMonic_X_sub_C_frontier_le Omega p
  refine ⟨C * Q, mul_nonneg hC hQ, ?_⟩
  intro xi hxi r hr t ht
  have hsigma : Omega.boundaryParam t ∈ frontier Omega.carrier := by
    rw [← Omega.boundaryParam_range]
    exact mem_range_self t
  calc
    ‖deriv Omega.boundaryParam t •
          (((star (Polynomial.eval (Omega.boundaryParam t) p) -
                star (Polynomial.eval xi p)) *
              (Omega.boundaryParam t -
                smoothJordanInwardPoint c xi r)⁻¹) -
            ((star (Polynomial.eval (Omega.boundaryParam t) p) -
                star (Polynomial.eval xi p)) *
              (Omega.boundaryParam t - xi)⁻¹))‖ ≤
        C * (‖deriv Omega.boundaryParam t‖ *
          ‖Polynomial.eval (Omega.boundaryParam t)
            (p /ₘ (Polynomial.X - Polynomial.C xi))‖) :=
      hdom xi hxi r hr t ht
    _ ≤ C * (‖deriv Omega.boundaryParam t‖ * Q) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hq xi hxi _ hsigma) (norm_nonneg _)) hC
    _ = (C * Q) * ‖deriv Omega.boundaryParam t‖ := by ring
