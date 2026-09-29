-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_existsUnique_hom_spec_comp_eq_of_natural
-- name    : AlgebraicGeometry.Scheme.existsUnique_hom_spec_comp_eq_of_natural
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/f2e6c349-5727-5d22-ad65-6d720952a059
-- title:
--   Yoneda for affine-valued points: morphisms from natural families
-- statement:
--   Let $R$ be a commutative ring and let $fZ \colon Z \to \operatorname{Spec} R$ and $fY \colon Y \to \operatorname{Spec} R$ be schemes over $\operatorname{Spec} R$ (all in a single universe). Suppose given a family $\eta$ which assigns, to every commutative $R$-algebra $C$ and every morphism $z \colon \operatorname{Spec} C \to Z$ whose composite with $fZ$ is the structure morphism $\operatorname{Spec}$ of $R \to C$, a morphism $\eta_C(z) \colon \operatorname{Spec} C \to Y$. Assume: (i) each $\eta_C(z)$ followed by $fY$ is again $\operatorname{Spec}$ of $R \to C$, that is, $\eta_C(z)$ is a morphism over $\operatorname{Spec} R$; (ii) $\eta$ is natural, in the sense that for every homomorphism of $R$-algebras $\varphi \colon C \to C'$, every $z$ as above, and every proof that $\operatorname{Spec}\varphi$ followed by $z$ again lies over $\operatorname{Spec} R$, one has $\eta_{C'}(z \circ \operatorname{Spec}\varphi) = \eta_C(z) \circ \operatorname{Spec}\varphi$. Then there exists a morphism of schemes $u \colon Z \to Y$ such that $u$ followed by $fY$ equals $fZ$, such that $u \circ z = \eta_C(z)$ for every $R$-algebra $C$ and every $z \colon \operatorname{Spec} C \to Z$ over $\operatorname{Spec} R$, and such that any morphism $v \colon Z \to Y$ satisfying $v \circ z = \eta_C(z)$ for all such $C$ and $z$ equals $u$. The uniqueness clause requires only compatibility with $\eta$ on affine-valued points, not that $v$ be a morphism over $\operatorname{Spec} R$.
--
--   This is the Yoneda lemma for the functor of points of a scheme over $R$ restricted to affine test schemes: a morphism $Z \to Y$ of $R$-schemes is determined by, and may be assembled from, its effect on $C$-valued points for commutative $R$-algebras $C$, provided the prescribed effect is natural in $C$. It is used throughout the project to produce morphisms of schemes from functorial constructions on points, for instance in the recognition of fine moduli problems, in comparisons of Galois-twisted points, and in the construction of morphisms out of nilpotent thickenings of points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_existsUnique_hom_spec_comp_eq_of_natural.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.existsUnique_hom_spec_comp_eq_of_natural
    {R : Type u} [CommRing R] {Z Y : Scheme.{u}}
    (fZ : Z ⟶ Spec (CommRingCat.of R)) (fY : Y ⟶ Spec (CommRingCat.of R))

    (η : ∀ (C : Type u) [CommRing C] [Algebra R C] (z : Spec (CommRingCat.of C) ⟶ Z),
      z ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap R C)) → (Spec (CommRingCat.of C) ⟶ Y))

    (hη_over : ∀ (C : Type u) [CommRing C] [Algebra R C] (z : Spec (CommRingCat.of C) ⟶ Z)
      (hz : z ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap R C))),
      η C z hz ≫ fY = Spec.map (CommRingCat.ofHom (algebraMap R C)))

    (hη_nat : ∀ (C C' : Type u) [CommRing C] [Algebra R C] [CommRing C'] [Algebra R C'] (φ : C →ₐ[R] C')
      (z : Spec (CommRingCat.of C) ⟶ Z) (hz : z ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap R C)))
      (hz' : (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ z) ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap R C'))),
      η C' (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ z) hz' = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ η C z hz) :
    ∃ u : Z ⟶ Y, u ≫ fY = fZ ∧
      (∀ (C : Type u) [CommRing C] [Algebra R C] (z : Spec (CommRingCat.of C) ⟶ Z)
        (hz : z ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap R C))), z ≫ u = η C z hz) ∧
      ∀ v : Z ⟶ Y,
        (∀ (C : Type u) [CommRing C] [Algebra R C] (z : Spec (CommRingCat.of C) ⟶ Z)
          (hz : z ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap R C))), z ≫ v = η C z hz) → v = u := by sorry
