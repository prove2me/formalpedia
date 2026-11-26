-- Prove2me | solution 1 for polynomialSupNorm_closure_carrier_eq_frontier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:57:35.507611+00:00
-- url     : https://prove2.me/submissions/bef6bb76-09f3-406a-bbd1-098868b28419

import Mathlib.Analysis.Complex.AbsMax
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_GeneralSymmetrized
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Theorems.Thm_polynomialSupNorm_closure_eq_frontier_of_isBounded

set_option autoImplicit false
open Complex Polynomial Set
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier) :
    polynomialSupNorm p (closure Omega.carrier) =
      polynomialSupNorm p (frontier Omega.carrier) :=
  polynomialSupNorm_closure_eq_frontier_of_isBounded p hbounded
