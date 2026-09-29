-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_linMap_map_comp_map
-- name    : AlgebraicGeometry.ProjSpace.linMap_map_comp_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/0fa105dc-bb60-5d56-8aaf-77156dbc970a
-- title:
--   Linear maps on Pⁿ commute with base change
-- statement:
--   Let $R$ and $A$ be commutative rings in the same universe with $A$ an $R$-algebra, let $n$ be a natural number, and let $M$ be an $(n+1)\times(n+1)$ matrix over $R$. Assume $M$ is a unit in the matrix ring over $R$, and that the matrix $M$.`map` $($`algebraMap R A`$)$, obtained by applying the structure map $R \to A$ entrywise, is a unit in the matrix ring over $A$. Here `ProjSpace.map R A n` is the morphism $\operatorname{Proj}\mathcal{A}_A \to \operatorname{Proj}\mathcal{A}_R$ induced, via `Proj.map`, by the graded ring homomorphism `MvPolynomial.map (algebraMap R A)` between the homogeneous-component algebras of $R[x_0,\dots,x_n]$ and $A[x_0,\dots,x_n]$, and `ProjSpace.linMap` of a unit matrix is the morphism induced by the graded homomorphism `linSubst`, the evaluation substituting for each variable the linear form attached to the matrix. The assertion is the commutativity of the base-change square: the morphism `ProjSpace.linMap A n` for the image matrix, followed by `ProjSpace.map R A n`, equals `ProjSpace.map R A n` followed by `ProjSpace.linMap R n M hM`, as morphisms $\operatorname{Proj}\mathcal{A}_A \to \operatorname{Proj}\mathcal{A}_R$.
--
--   This is the compatibility of the linear (projective-linear) action on $\mathbb{P}^n$ with base change along $R \to A$, expressed at the level of $\operatorname{Proj}$ of the graded polynomial algebras. It is used in the treatment of framed polarised abelian schemes, where the pullback clauses of the level-structure statements require the linear intertwiners to be compatible with change of base ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_linMap_map_comp_map.lean

import Definitions.Def_AlgebraicGeometry_ProjSpaceLinMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.linMap_map_comp_map {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (n : ℕ)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (hM : IsUnit M) (hMA : IsUnit (M.map (algebraMap R A))) :
    ProjSpace.linMap A n (M.map (algebraMap R A)) hMA ≫ ProjSpace.map R A n =
      ProjSpace.map R A n ≫ ProjSpace.linMap R n M hM := by sorry
