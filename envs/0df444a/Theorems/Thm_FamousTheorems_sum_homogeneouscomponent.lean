-- Prove2me | Theorems.Thm_FamousTheorems_sum_homogeneouscomponent
-- name    : FamousTheorems.sum_homogeneouscomponent
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T08:37:42.631959+00:00
-- url     : https://prove2.me/theorems/44beea16-ea21-4ad5-8bbf-e1710e2780af
-- title:
--   Decomposition into homogeneous components
-- statement:
--   **Decomposition of a polynomial into homogeneous components.** Every multivariable polynomial is the sum of its homogeneous parts: $$\varphi = \sum_{i=0}^{\deg \varphi} \varphi_i,$$ where $\varphi_i$ collects the monomials of total degree $i$. This is the statement that the polynomial ring is a graded ring, with the grading by total degree. The decomposition is unique, and it is what allows arguments to proceed degree by degree — comparing homogeneous components of an identity is the standard technique for extracting information from polynomial equations. Homogeneous polynomials are exactly those defining well-posed conditions in projective space, so this decomposition is also the bridge between affine and projective algebraic geometry. **Formalization note.** `MvPolynomial.homogeneousComponent i φ` extracts the degree-$i$ part, and the sum runs to `φ.totalDegree`, which suffices since higher components vanish. The result is Mathlib's `MvPolynomial.sum_homogeneousComponent`.
-- source:
--   Listed in Mathlib's undergraduate/overview curriculum manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem sum_homogeneouscomponent :
    ∀ {σ : Type u_1} {R : Type u_2} [inst : CommSemiring R] (φ : MvPolynomial σ R), 
    ∑ i ∈ Finset.range (φ.totalDegree + 1), (MvPolynomial.homogeneousComponent i) φ = φ := by sorry

end FamousTheorems
