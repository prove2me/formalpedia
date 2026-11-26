-- Prove2me | solution 1 for polynomialSupNorm_carrier_eq_frontier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:21:53.674245+00:00
-- url     : https://prove2.me/submissions/4a2b4e89-ee27-4348-9671-3415949a93b3

import Mathlib.Analysis.Complex.AbsMax
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Theorems.Thm_polynomialSupNorm_closure_carrier_eq_frontier
import Theorems.Thm_polynomialSupNorm_closure_of_isBounded

set_option autoImplicit false
open Complex Polynomial Set
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier) :
    polynomialSupNorm p Omega.carrier =
      polynomialSupNorm p (frontier Omega.carrier) := by
  rw [← polynomialSupNorm_closure_of_isBounded p hbounded]
  exact polynomialSupNorm_closure_carrier_eq_frontier Omega p hbounded
