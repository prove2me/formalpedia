-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_kPointOfVec_chart
-- name    : AlgebraicGeometry.ProjSpace.kPointOfVec_chart
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:07:26.232208+00:00
-- url     : https://prove2.me/theorems/54ca3482-8f2d-48fa-9bab-e2ada39b06a4
-- title:
--   A nonzero coordinate gives the affine-chart description of a projective point
-- statement:
--   Let $v=(v_0,…,v_N)∈K^{N+1}$ be nonzero and suppose $v_i≠0$. Then there is a ring map $φ$ from the homogeneous localization at $X_i$ to $K$ such that $$φ(X_j/X_i)=v_j/v_i\quad\text{for every }j,$$ and the projective point $[v]$ factors through the basic open $D_+(X_i)$ via $Spec(φ)$. This supplies explicit affine coordinates for a projective point.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpacePoints

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry

theorem AlgebraicGeometry.ProjSpace.kPointOfVec_chart (K : Type) [Field K] (N : ℕ) (v : Fin (N + 1) → K) (hv : v ≠ 0)
    (i : Fin (N + 1)) (hi : v i ≠ 0) :
    ∃ φ : HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (MvPolynomial.X i) →+* K,
      (∀ j, φ (ProjSpace.ratio K N i j) = v j / v i) ∧
      (ProjSpace.kPointOfVec K N v hv).1 = Spec.map (CommRingCat.ofHom φ) ≫
        Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (MvPolynomial.X i)
          (ProjSpace.X_mem_one K N i) one_pos := by sorry
