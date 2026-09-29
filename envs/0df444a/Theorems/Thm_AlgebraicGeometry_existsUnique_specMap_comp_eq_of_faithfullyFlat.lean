-- Prove2me | Theorems.Thm_AlgebraicGeometry_existsUnique_specMap_comp_eq_of_faithfullyFlat
-- name    : AlgebraicGeometry.existsUnique_specMap_comp_eq_of_faithfullyFlat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/e4e4b9d1-0399-5a92-b02d-8282ac867a94
-- title:
--   Unique descent of a T-point along a faithfully flat algebra
-- statement:
--   Let $B$ and $B'$ be commutative rings with $B'$ a $B$-algebra, and assume $B'$ is faithfully flat as a $B$-module. Let $T$ be a scheme and let $\varphi' \colon \operatorname{Spec} B' \to T$ be a morphism of schemes. Consider the two $B'$-algebra structure maps into $B' \otimes_B B'$, namely the inclusion into the left factor (`Algebra.TensorProduct.includeLeftRingHom`) and the inclusion into the right factor (`Algebra.TensorProduct.includeRight`), and the two induced morphisms $\operatorname{Spec}(B' \otimes_B B') \to \operatorname{Spec} B'$. The hypothesis is that the composites of these two morphisms with $\varphi'$ agree, i.e. $\varphi'$ has equal pull-backs along the two projections. The conclusion asserts the existence of a unique morphism $\varphi \colon \operatorname{Spec} B \to T$ such that the morphism $\operatorname{Spec} B' \to \operatorname{Spec} B$ induced by the structure map $B \to B'$, followed by $\varphi$, equals $\varphi'$. All rings and the scheme $T$ live in a single universe $u$.
--
--   This is Grothendieck's statement that the functor of points of a scheme is a sheaf for the fpqc topology, in the affine-cover-free form of an equaliser diagram $T(B) \to T(B') \rightrightarrows T(B' \otimes_B B')$. It is used in the project to descend morphisms of schemes along faithfully flat ring extensions, for instance in the construction of pullback squares and comparison isomorphisms for polarised abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_existsUnique_specMap_comp_eq_of_faithfullyFlat.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

theorem AlgebraicGeometry.existsUnique_specMap_comp_eq_of_faithfullyFlat
    {B B' : Type u} [CommRing B] [CommRing B'] [Algebra B B'] [Module.FaithfullyFlat B B']
    {T : Scheme.{u}} (φ' : Spec (CommRingCat.of B') ⟶ T)
    (h : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : B' →+* B' ⊗[B] B')) ≫ φ' =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B' →ₐ[B] B' ⊗[B] B').toRingHom) ≫ φ') :
    ∃! φ : Spec (CommRingCat.of B) ⟶ T, Spec.map (CommRingCat.ofHom (algebraMap B B')) ≫ φ = φ' := by sorry
