-- Prove2me | Theorems.Thm_AlgebraicGeometry_epi_specMap_of_injective_of_finite
-- name    : AlgebraicGeometry.epi_specMap_of_injective_of_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/aae2d32b-b93b-5882-816b-030149e30981
-- title:
--   Spec of an injective finite ring map is an epimorphism
-- statement:
--   Let $A$ and $B$ be commutative rings (in a fixed universe) and let $\varphi \colon A \to B$ be a ring homomorphism. Assume that $\varphi$ is injective as a function, and that $\varphi$ is finite, i.e. $B$ is a finitely generated module over $A$ via $\varphi$. Then the induced morphism of affine schemes $\operatorname{Spec}\varphi \colon \operatorname{Spec} B \to \operatorname{Spec} A$, obtained by applying the functor $\operatorname{Spec}$ to $\varphi$ viewed as a morphism of commutative rings, is an epimorphism in the category of schemes: for every scheme $Z$ and every pair of morphisms $u, v \colon \operatorname{Spec} A \to Z$ with $\operatorname{Spec}\varphi$ followed by $u$ equal to $\operatorname{Spec}\varphi$ followed by $v$, one has $u = v$. No flatness, faithful flatness or surjectivity assumption beyond the two stated hypotheses is imposed.
--
--   This is the standard criterion that a surjective, scheme-theoretically dominant morphism of schemes is an epimorphism, applied to the spectrum of an injective finite ring extension. It is used in the treatment of polarised abelian schemes, for producing points after a finite free base change, and in the construction of the base-changed Raynaud quotient attached to the level torsion of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_epi_specMap_of_injective_of_finite.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem AlgebraicGeometry.epi_specMap_of_injective_of_finite
    {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (hφ : Function.Injective φ) (hfin : φ.Finite) :
    CategoryTheory.Epi (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)) := by sorry
