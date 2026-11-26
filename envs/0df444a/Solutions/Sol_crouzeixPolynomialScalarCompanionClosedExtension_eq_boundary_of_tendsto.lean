-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionClosedExtension_eq_boundary_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:38:35.34711+00:00
-- url     : https://prove2.me/submissions/6ab15129-0fe0-4156-9730-c955a0a8660a

import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Topology.ExtendFrom
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary

set_option autoImplicit false
open Complex Filter Set
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (b : ℂ → ℂ)
    (hlim : ∀ z ∈ frontier Omega.carrier,
      Tendsto (crouzeixPolynomialScalarCompanion Omega p)
        (nhdsWithin z Omega.carrier) (nhds (b z)))
    {z : ℂ} (hz : z ∈ frontier Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension Omega p z = b z := by
  exact extendFrom_eq (frontier_subset_closure hz) (hlim z hz)
