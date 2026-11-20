-- Prove2me | Theorems.Thm_DualSepClusterLP_positiveTriangleEndpointCertificate
-- name    : DualSepClusterLP.positiveTriangleEndpointCertificate
-- status  : Proved
-- author  : @hypercube
-- created : 2026-11-19T07:55:57.965278+00:00
-- url     : https://prove2.me/theorems/74be4468-aa39-4755-9d9f-c9d70ee84a1a
-- title:
--   Lemma 7.3 — endpoint inequalities for triangles with at least two positive edges
-- statement:
--   Take three edges in cyclic order and pair masses $x,y,z$ in the unit interval. Suppose that at least two signs are positive. The joint triple mass ranges from the maximum of $0,x+y-1,y+z-1,z+x-1$ to the minimum of $x,y,z$. Whenever this interval is nonempty, the sum over the three pivots of the expected released budget less payment and its covariance correction is nonnegative at both endpoints. The specified rules use the exact rational constants $2773/2000$, $13/6$, and $1012/25$.
-- source:
--   David García-Soriano and Antoine Schohn, Approximate Dual Separation for the Cluster LP, STOC 2027 paper 79, §7.3–7.4, equations (38)–(47), Lemma 7.3 and Appendix C. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/79.pdf

import Definitions.Def_DualSepClusterLP_RoundingAnalysis

namespace DualSepClusterLP

/-- The sign patterns with at least two positive edges of Lemma 7.3 at the two feasible
endpoints of the triple mass. Triangles with zero or one positive edge are handled analytically. -/
theorem positiveTriangleEndpointCertificate (s₁ s₂ s₃ : Bool)
    (hs : (s₁ = true ∧ s₂ = true) ∨ (s₂ = true ∧ s₃ = true) ∨ (s₃ = true ∧ s₁ = true))
    (x y z : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) (hy : y ∈ Set.Icc (0:ℝ) 1)
    (hz : z ∈ Set.Icc (0:ℝ) 1) (hn : tripleLower x y z ≤ tripleUpper x y z) :
    0 ≤ signedTriangleSurplus s₁ s₂ s₃ x y z (tripleLower x y z) ∧
    0 ≤ signedTriangleSurplus s₁ s₂ s₃ x y z (tripleUpper x y z) := by sorry

end DualSepClusterLP
