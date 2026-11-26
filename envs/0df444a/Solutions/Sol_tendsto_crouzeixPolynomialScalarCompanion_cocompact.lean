-- Prove2me | solution 1 for tendsto_crouzeixPolynomialScalarCompanion_cocompact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:43:47.996742+00:00
-- url     : https://prove2.me/submissions/38d58a4c-924d-43be-ae35-f26fa1a23877

import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Theorems.Thm_exists_nonneg_bound_crouzeixPolynomialScalarCompanionNumerator
import Theorems.Thm_norm_crouzeixPolynomialScalarCompanion_le_infDist
import Theorems.Thm_tendsto_infDist_frontier_cocompact_atTop
import Theorems.Thm_SmoothJordanDomain_isCompact_frontier
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
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) :
    Tendsto (crouzeixPolynomialScalarCompanion Omega p)
      (cocompact ℂ) (nhds 0) := by
  obtain ⟨C, hC_nonneg, hC⟩ :=
    exists_nonneg_bound_crouzeixPolynomialScalarCompanionNumerator Omega p
  have hinf := tendsto_infDist_frontier_cocompact_atTop Omega
  have hinv : Tendsto
      (fun z : ℂ ↦ (Metric.infDist z (frontier Omega.carrier))⁻¹)
      (cocompact ℂ) (nhds 0) := hinf.inv_tendsto_atTop
  have hmajorant : Tendsto
      (fun z : ℂ ↦ ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
        (2 * Real.pi *
          (C * (Metric.infDist z (frontier Omega.carrier))⁻¹)))
      (cocompact ℂ) (nhds 0) := by
    have hscaled :=
      (tendsto_const_nhds.mul hinv : Tendsto
        (fun z : ℂ ↦
          (‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * (2 * Real.pi * C)) *
            (Metric.infDist z (frontier Omega.carrier))⁻¹)
        (cocompact ℂ) (nhds
          ((‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * (2 * Real.pi * C)) * 0)))
    simpa only [mul_zero] using hscaled.congr'
      (Eventually.of_forall fun z ↦ by ring)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
    (Eventually.of_forall fun z ↦ norm_nonneg
      (crouzeixPolynomialScalarCompanion Omega p z))
  · filter_upwards [Omega.isCompact_frontier.compl_mem_cocompact] with z hz
    exact norm_crouzeixPolynomialScalarCompanion_le_infDist
      Omega p hC_nonneg hC hz
  · exact hmajorant
