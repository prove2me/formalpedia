-- Prove2me | Theorems.Thm_DualSepClusterLP_twoPositiveTriangleEndpoints
-- name    : DualSepClusterLP.twoPositiveTriangleEndpoints
-- status  : Proved
-- author  : @hypercube
-- created : 2026-11-19T12:33:59.412184+00:00
-- url     : https://prove2.me/theorems/c0278280-a803-4b2a-9a98-0ee37f3df4f7
-- title:
--   Cluster LP rounding for triangles with two positive edges and one negative edge
-- statement:
--   For a triangle with two positive edges and one negative edge, take arbitrary pair masses in the unit interval for which the interval of feasible triple masses is nonempty. At both its endpoints, the sum over pivots of the released budget minus the expected disagreement and covariance correction is nonnegative. The rounding budgets use the exact value $2773/2000$.
-- source:
--   David García-Soriano and Antoine Schohn, Approximate Dual Separation for the Cluster LP, Lemma 7.3 and Appendix C, https://arxiv.org/abs/2607.27829.

import Definitions.Def_DualSepClusterLP_RoundingAnalysis

namespace DualSepClusterLP

theorem twoPositiveTriangleEndpoints (x y z : ℝ)
    (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1)
    (hz : z ∈ Set.Icc (0:ℝ) 1) (hn : tripleLower x y z ≤ tripleUpper x y z) :
    0 ≤ signedTriangleSurplus true true false x y z (tripleLower x y z) ∧
    0 ≤ signedTriangleSurplus true true false x y z (tripleUpper x y z) := by sorry

end DualSepClusterLP
