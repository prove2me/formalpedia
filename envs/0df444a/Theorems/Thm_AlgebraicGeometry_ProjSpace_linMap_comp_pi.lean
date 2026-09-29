-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_linMap_comp_pi
-- name    : AlgebraicGeometry.ProjSpace.linMap_comp_pi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/77a30d40-4af4-571c-a21b-650c0ede7b79
-- title:
--   Linear maps on Pⁿ_R commute with the structure morphism
-- statement:
--   Let $R$ be a commutative ring, let $n$ be a natural number, let $M$ be an $(n+1)\times(n+1)$ matrix over $R$, and suppose $M$ is a unit in the matrix ring. Write $\mathcal{A}$ for the graded algebra given by the homogeneous submodules of $\mathrm{MvPolynomial}\ (\mathrm{Fin}\ (n+1))\ R$, so that $\mathrm{Proj}\ \mathcal{A}$ is projective $n$-space over $R$. The morphism `ProjSpace.linMap R n M hM : Proj 𝒜 ⟶ Proj 𝒜` is `Proj.map` applied to the graded ring homomorphism `ProjSpace.linSubst R n M`, namely the evaluation homomorphism of $\mathcal{A}$ sending the variable $x_i$ to the linear form $\sum_j M_{ij} x_j$ (grading-preserving because these substituted forms are homogeneous of degree one), together with the hypothesis `irrelevant_le_map_linSubst R n M hM` that the irrelevant ideal behaves as required under this substitution, which uses the invertibility of $M$. The assertion is that `ProjSpace.linMap R n M hM` followed by the structure morphism `ProjSpace.π R n : Proj 𝒜 ⟶ Spec R` equals `ProjSpace.π R n`; that is, the linear map is a morphism of schemes over $\operatorname{Spec} R$.
--
--   This records that the projective linear automorphism attached to an invertible matrix is a morphism over the base, the standard compatibility of a linear change of homogeneous coordinates with the structure morphism of $\mathbb{P}^n_R$. It is used in the 'over $\operatorname{Spec} R$' bookkeeping of statements about $\mathrm{Proj}$ presentations of modules and about framed polarised abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_linMap_comp_pi.lean

import Definitions.Def_AlgebraicGeometry_ProjSpaceLinMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.linMap_comp_pi {R : Type u} [CommRing R] (n : ℕ)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (hM : IsUnit M) :
    ProjSpace.linMap R n M hM ≫ ProjSpace.π R n = ProjSpace.π R n := by sorry
