-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_kPointOfVec_mem_homogeneousIdeal_iff_eval
-- name    : AlgebraicGeometry.ProjSpace.kPointOfVec_mem_homogeneousIdeal_iff_eval
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:07:09.585197+00:00
-- url     : https://prove2.me/theorems/39a5a650-b4b8-4d3c-a20b-3609afbbc896
-- title:
--   A homogeneous ideal is contained in the ideal of $[z]$ exactly when all its elements vanish
-- statement:
--   Let $z∈K^{N+1}$ be nonzero and let $I$ be a homogeneous ideal. Then $$I⊆I([z])\iff p(z)=0\text{ for every }p∈I.$$ This packages the evaluation criterion at the level of homogeneous ideals.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpacePoints

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory AlgebraicGeometry HomogeneousLocalization MvPolynomial
open AlgebraicGeometry
open AlgebraicGeometry.ProjSpace

theorem AlgebraicGeometry.ProjSpace.kPointOfVec_mem_homogeneousIdeal_iff_eval {K : Type} [Field K] {N : ℕ}
    (z : Fin (N + 1) → K) (hz : z ≠ 0)
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin (N + 1)) K)) :
    I ≤ ((kPointOfVec K N z hz).1 (IsLocalRing.closedPoint K)).asHomogeneousIdeal ↔
      ∀ p ∈ I.toIdeal, eval z p = 0 := by sorry
