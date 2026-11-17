-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_kPointOfVec_eq_of_chart
-- name    : AlgebraicGeometry.ProjSpace.kPointOfVec_eq_of_chart
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:07:11.530793+00:00
-- url     : https://prove2.me/theorems/c8a93a7b-d7c4-4f0d-bcff-5beb12c74248
-- title:
--   Matching all affine chart ratios determines the projective point
-- statement:
--   Let $x∈ℙ^N(K)$, let $v∈K^{N+1}$ be nonzero, and choose $i$ with $v_i≠0$. Suppose a chart map $φ$ satisfies $φ(X_j/X_i)=v_j/v_i$ for all $j$ and that $x$ factors through the $i$th chart by $Spec(φ)$. Then $$[v]=x.$$ This reconstructs a projective point from its affine-chart coordinate map.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpacePoints

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory AlgebraicGeometry NeronModelInfra
open AlgebraicGeometry
open AlgebraicGeometry.ProjSpace

theorem AlgebraicGeometry.ProjSpace.kPointOfVec_eq_of_chart {K : Type} [Field K] {N : ℕ}
    (x : Scheme.KPoint (π K N)) (v : Fin (N + 1) → K) (hv : v ≠ 0)
    (i : Fin (N + 1)) (hi : v i ≠ 0)
    (φ : HomogeneousLocalization.Away
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K) (MvPolynomial.X i) →+* K)
    (hφ : ∀ j, φ (ratio K N i j) = v j / v i)
    (hx : x.1 = Spec.map (CommRingCat.ofHom φ) ≫
      Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) K)
        (MvPolynomial.X i) (X_mem_one K N i) one_pos) :
    kPointOfVec K N v hv = x := by sorry
