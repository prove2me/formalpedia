-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_map_preimage_basicOpen_X
-- name    : AlgebraicGeometry.ProjSpace.map_preimage_basicOpen_X
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/70e3791e-dd99-543a-a9e2-94aff2bd9c9d
-- title:
--   Base change of Pⁿ preserves the standard charts
-- statement:
--   Let $R$ and $A$ be commutative rings in a common universe, with $A$ an $R$-algebra, let $n$ be a natural number and let $j$ be an index in $\mathrm{Fin}(n+1)$. Write $\mathcal{A}_R$ for the graded algebra $\mathrm{MvPolynomial.homogeneousSubmodule}\,(\mathrm{Fin}(n+1))\,R$, that is the grading of $R[x_0,\dots,x_n]$ by homogeneous components, and similarly $\mathcal{A}_A$ over $A$. The morphism `ProjSpace.map R A n` from $\mathrm{Proj}\,\mathcal{A}_A$ to $\mathrm{Proj}\,\mathcal{A}_R$ is `Proj.map` applied to the graded ring homomorphism `mvMapGraded`, namely coefficientwise application of the structure map $R \to A$, which carries homogeneous polynomials of each degree to homogeneous polynomials of the same degree, together with the inclusion of the irrelevant ideal in the preimage of the irrelevant ideal supplied by `irrelevant_le_map_mvMapGraded`. The assertion is an equality of open subsets of $\mathrm{Proj}\,\mathcal{A}_A$: the preimage under this morphism of the basic open subset $D_+(x_j) =$ `Proj.basicOpen` $\mathcal{A}_R\,(x_j)$ of $\mathrm{Proj}\,\mathcal{A}_R$ is exactly the basic open subset `Proj.basicOpen` $\mathcal{A}_A\,(x_j)$ of $\mathrm{Proj}\,\mathcal{A}_A$.
--
--   This records that the base-change morphism $\mathbb{P}^n_A \to \mathbb{P}^n_R$ is compatible with the standard affine charts $D_+(x_j)$, so that the standard cover of projective space may be transported along base change. It is used, together with the pullback square for base change of projective space, in the treatment of coherence and finiteness for sheaves on Proj-presentations and in the Hilbert functor material.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_map_preimage_basicOpen_X.lean

import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

theorem AlgebraicGeometry.ProjSpace.map_preimage_basicOpen_X (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (n : ℕ) (j : Fin (n + 1)) :
    ProjSpace.map R A n ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X j)
      = Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X j) := by sorry
