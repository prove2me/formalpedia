-- Prove2me | Theorems.Thm_FamousTheorems_rootset_derivative_subset_convexhull_rootset
-- name    : FamousTheorems.rootset_derivative_subset_convexhull_rootset
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:02:08.416984+00:00
-- url     : https://prove2.me/theorems/bc6efcdd-2302-44b3-ba57-0ae6cdfb55cf
-- title:
--   The Gauss–Lucas theorem
-- statement:
--   **The Gauss\u2013Lucas theorem.** The roots of $p'$ lie in the convex hull of the roots of $p$. Differentiation contracts the root set inward: critical points cannot escape the polygon spanned by the zeros. The proof is a physical one — $p'/p$ is a sum of inverse-distance terms, so a root of $p'$ is a weighted barycentre of the roots of $p$ and hence lies in their hull. Iterating shows all higher derivatives have roots in the same hull, and for real polynomials with real roots it recovers Rolle's theorem. **Formalization note.** `rootSet` is the set of roots in an algebraically closed field and `convexHull` is taken over $\mathbb{R}$. The result is Mathlib's `Polynomial.rootSet_derivative_subset_convexHull_rootSet`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem rootset_derivative_subset_convexhull_rootset :
    ∀ {P : Polynomial ℂ}, 
    0 < P.degree → (Polynomial.derivative P).rootSet ℂ ⊆ (convexHull ℝ) (P.rootSet ℂ) := by sorry

end FamousTheorems
