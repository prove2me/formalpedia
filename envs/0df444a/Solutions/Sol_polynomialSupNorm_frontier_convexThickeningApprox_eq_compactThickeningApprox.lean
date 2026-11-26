-- Prove2me | solution 1 for polynomialSupNorm_frontier_convexThickeningApprox_eq_compactThickeningApprox
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:41:51.957412+00:00
-- url     : https://prove2.me/submissions/16e4b5f7-1e81-46c0-a97e-f66c392cc109

import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_BoundaryMaximum
import Definitions.Def_Operator_Crouzeix_CompactThickeningApprox
import Definitions.Def_Operator_Crouzeix_BoundaryApproximation
import Theorems.Thm_polynomialSupNorm_closure_eq_frontier_of_isBounded

section
open Filter Polynomial Set
private theorem smoothApproxRadius_pos_boundary (n : ℕ) :
    0 < smoothApproxRadius n := by
  unfold smoothApproxRadius
  positivity
end

set_option autoImplicit false
open Filter Polynomial Set
theorem _root_.solution
    (p : Polynomial ℂ) {K : Set ℂ} (hK : Bornology.IsBounded K) (n : ℕ) :
    polynomialSupNorm p (frontier (convexThickeningApprox K n)) =
      polynomialSupNorm p (compactThickeningApprox K n) := by
  have hbounded : Bornology.IsBounded (convexThickeningApprox K n) := by
    exact hK.thickening
  rw [← polynomialSupNorm_closure_eq_frontier_of_isBounded p hbounded]
  congr 1
  exact closure_thickening (smoothApproxRadius_pos_boundary n) K
