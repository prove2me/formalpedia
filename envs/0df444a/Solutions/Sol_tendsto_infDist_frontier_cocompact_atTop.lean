-- Prove2me | solution 1 for tendsto_infDist_frontier_cocompact_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:41:56.745784+00:00
-- url     : https://prove2.me/submissions/00f461c0-af6e-4175-8a94-bf67a2153193

import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Theorems.Thm_SmoothJordanDomain_isCompact_frontier


set_option autoImplicit false
open Complex Filter Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) :
    Tendsto (fun z : ℂ ↦ Metric.infDist z (frontier Omega.carrier))
      (cocompact ℂ) atTop := by
  let y : ℂ := Omega.boundaryParam 0
  have hy : y ∈ frontier Omega.carrier := by
    rw [← Omega.boundaryParam_range]
    exact mem_range_self 0
  have hdist : Tendsto (fun z : ℂ ↦ dist z y) (cocompact ℂ) atTop :=
    tendsto_dist_right_cocompact_atTop y
  have hshift : Tendsto
      (fun z : ℂ ↦ dist z y + (-Metric.diam (frontier Omega.carrier)))
      (cocompact ℂ) atTop :=
    tendsto_atTop_add_const_right (cocompact ℂ)
      (-Metric.diam (frontier Omega.carrier)) hdist
  refine tendsto_atTop_mono' (cocompact ℂ) ?_ hshift
  filter_upwards with z
  have hbound := Metric.dist_le_infDist_add_diam
    (x := z) Omega.isCompact_frontier.isBounded hy
  linarith
