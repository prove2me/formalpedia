-- Prove2me | solution 1 for frontier_convexThickeningApprox_subset_compactThickeningApprox
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:49:14.734239+00:00
-- url     : https://prove2.me/submissions/66d93fff-fc61-49bf-8c56-e2280e45b8a2

import Definitions.Def_Operator_Crouzeix_SmoothApprox
import Definitions.Def_Operator_Crouzeix_CompactThickeningApprox

set_option autoImplicit false
open Metric Set
theorem _root_.solution
    (K : Set ℂ) (n : ℕ) :
    frontier (convexThickeningApprox K n) ⊆ compactThickeningApprox K n := by
  exact frontier_subset_closure.trans
    (Metric.closure_thickening_subset_cthickening (smoothApproxRadius n) K)
