-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_kPointOfVec_mem_iff_eval
-- name    : AlgebraicGeometry.ProjSpace.kPointOfVec_mem_iff_eval
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:07:33.982773+00:00
-- url     : https://prove2.me/theorems/f3e38fa4-9e08-45a0-8e85-3dd989ea6702
-- title:
--   A homogeneous polynomial belongs to the ideal of $[z]$ exactly when it vanishes at $z$
-- statement:
--   Let $z∈K^{N+1}$ be nonzero, and let $p$ be a homogeneous polynomial of degree $d$. Then $$p∈I([z])\iff p(z)=0.$$ This is the pointwise evaluation criterion for homogeneous ideals in projective space.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpacePoints

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory AlgebraicGeometry HomogeneousLocalization MvPolynomial
open AlgebraicGeometry
open AlgebraicGeometry.ProjSpace

theorem AlgebraicGeometry.ProjSpace.kPointOfVec_mem_iff_eval {K : Type} [Field K] {N : ℕ}
    (z : Fin (N + 1) → K) (hz : z ≠ 0)
    (p : MvPolynomial (Fin (N + 1)) K) (d : ℕ) (hp : p.IsHomogeneous d) :
    p ∈ ((kPointOfVec K N z hz).1 (IsLocalRing.closedPoint K)).asHomogeneousIdeal ↔
      eval z p = 0 := by sorry
