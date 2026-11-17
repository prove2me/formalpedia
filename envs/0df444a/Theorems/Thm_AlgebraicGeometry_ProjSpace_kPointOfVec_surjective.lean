-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_kPointOfVec_surjective
-- name    : AlgebraicGeometry.ProjSpace.kPointOfVec_surjective
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:07:34.921811+00:00
-- url     : https://prove2.me/theorems/9500e0c2-5c00-4e99-a925-cef6fb2ed3dd
-- title:
--   Every rational point of projective space is represented by a nonzero vector
-- statement:
--   Let $K$ be a field and let $x∈ℙ^N(K)$. There exists a nonzero vector $v∈K^{N+1}$ such that $$[v]=x.$$ This provides homogeneous coordinates for arbitrary scheme-theoretic rational points.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpacePoints

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry

theorem AlgebraicGeometry.ProjSpace.kPointOfVec_surjective (K : Type) [Field K] (N : ℕ)
    (x : Scheme.KPoint (ProjSpace.π K N)) :
    ∃ (v : Fin (N + 1) → K) (hv : v ≠ 0), ProjSpace.kPointOfVec K N v hv = x := by sorry
