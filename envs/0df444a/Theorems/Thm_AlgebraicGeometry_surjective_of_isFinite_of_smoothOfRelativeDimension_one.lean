-- Prove2me | Theorems.Thm_AlgebraicGeometry_surjective_of_isFinite_of_smoothOfRelativeDimension_one
-- name    : AlgebraicGeometry.surjective_of_isFinite_of_smoothOfRelativeDimension_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/a5399f82-f15e-57a2-9603-8f776828d7e5
-- title:
--   Finite morphisms of smooth integral curves over a field are surjective
-- statement:
--   Let $k$ be a field and let $C$ and $U$ be schemes (in a fixed universe) equipped with morphisms $\pi_C : C \to \operatorname{Spec} k$ and $\pi_U : U \to \operatorname{Spec} k$, where $\operatorname{Spec} k$ is the spectrum of $k$ viewed as a commutative ring. Assume that $C$ and $U$ are integral schemes and that $\pi_C$ and $\pi_U$ are smooth of relative dimension $1$, i.e. $C$ and $U$ are smooth curves over $k$ in the sense of Mathlib's `SmoothOfRelativeDimension 1`. Let $c : C \to U$ be a morphism of schemes which commutes with the structure morphisms, $c$ followed by $\pi_U$ equal to $\pi_C$, and assume $c$ is a finite morphism. The conclusion is that the underlying continuous map of $c$ on topological spaces, `c.base`, is surjective as a function from the points of $C$ to the points of $U$.
--
--   This is the standard fact that a finite morphism between integral smooth curves over a field is surjective (finite morphisms are closed, and the image of the generic point must be the generic point). It is invoked in the study of a moduli tower of quaternionic type, where a degeneracy or covering map between smooth integral curves has to be shown to hit every point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_surjective_of_isFinite_of_smoothOfRelativeDimension_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.surjective_of_isFinite_of_smoothOfRelativeDimension_one
    {k : Type u} [Field k] {C U : Scheme.{u}}
    (πC : C ⟶ Spec (CommRingCat.of k)) (πU : U ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsIntegral U]
    [SmoothOfRelativeDimension 1 πC] [SmoothOfRelativeDimension 1 πU]
    (c : C ⟶ U) (hc : c ≫ πU = πC) [IsFinite c] :
    Function.Surjective c.base := by sorry
