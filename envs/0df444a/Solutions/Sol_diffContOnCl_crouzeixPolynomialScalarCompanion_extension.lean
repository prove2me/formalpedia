-- Prove2me | solution 1 for diffContOnCl_crouzeixPolynomialScalarCompanion_extension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:27:41.71064+00:00
-- url     : https://prove2.me/submissions/b2650653-b272-4292-8e6f-30c7267b36ce

import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.ExtendFrom
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Theorems.Thm_hasDerivAt_crouzeixPolynomialScalarCompanion


set_option autoImplicit false
open Complex Filter Set
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (g : ℂ → ℂ)
    (hcont : ContinuousOn g (closure Omega.carrier))
    (heq : Set.EqOn g (crouzeixPolynomialScalarCompanion Omega p)
      Omega.carrier) :
    DiffContOnCl ℂ g Omega.carrier := by
  refine ⟨?_, hcont⟩
  intro z hz
  have hev : g =ᶠ[nhds z]
      crouzeixPolynomialScalarCompanion Omega p := by
    filter_upwards [Omega.isOpen_carrier.mem_nhds hz] with w hw
    exact heq hw
  exact ((hasDerivAt_crouzeixPolynomialScalarCompanion Omega p hz).congr_of_eventuallyEq
    hev).differentiableAt.differentiableWithinAt
