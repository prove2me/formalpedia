-- Prove2me | Theorems.Thm_AlgebraicGeometry_SchemeHomOver_exists_iso_spec_of_forall_equiv_algHom
-- name    : AlgebraicGeometry.SchemeHomOver.exists_iso_spec_of_forall_equiv_algHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/8fd60fbb-1034-5f5f-81c6-7df36b9ac439
-- title:
--   Affine representability gives Spec H ≅ Y over Spec R
-- statement:
--   Let $R$ be a commutative ring, let $Y$ be a scheme equipped with a morphism $y : Y \to \operatorname{Spec} R$, and assume $Y$ is affine. Let $H$ be a commutative $R$-algebra, and suppose given, for every commutative $R$-algebra $T$, a bijection $E_T$ between the $R$-algebra homomorphisms $H \to T$ and the set of scheme morphisms $z : \operatorname{Spec} T \to Y$ satisfying $z$ followed by $y$ equals $\operatorname{Spec}$ of the structure map $R \to T$ (that is, elements of the subtype `SchemeHomOver` of morphisms over $\operatorname{Spec} R$). Suppose further that these bijections are natural: for all commutative $R$-algebras $T, T'$, every $R$-algebra homomorphism $a : T \to T'$ and every $\varphi : H \to T$, the underlying morphism of $E_{T'}(a \circ \varphi)$ equals $\operatorname{Spec}(a)$ followed by the underlying morphism of $E_T(\varphi)$. Then there exists an isomorphism of schemes $i : \operatorname{Spec} H \cong Y$ such that $i$ followed by $y$ is $\operatorname{Spec}$ of the structure map $R \to H$, and such that for every commutative $R$-algebra $T$ and every $R$-algebra homomorphism $\varphi : H \to T$, the underlying morphism of $E_T(\varphi)$ is $\operatorname{Spec}(\varphi)$ followed by $i$.
--
--   This is the affine case of Yoneda-style representability: an affine scheme over $\operatorname{Spec} R$ whose $T$-points over the base are functorially identified with $R$-algebra maps out of $H$ is canonically $\operatorname{Spec} H$ over $\operatorname{Spec} R$. It is used in the construction of scheme-theoretic kernels for relative group laws, where the representing algebra of a torsion condition is recognised as the coordinate ring of a given affine scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_SchemeHomOver_exists_iso_spec_of_forall_equiv_algHom.lean

import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.SchemeHomOver.exists_iso_spec_of_forall_equiv_algHom
    {R : Type u} [CommRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R)) [IsAffine Y]
    (H : Type u) [CommRing H] [Algebra R H]
    (E : ∀ (T : Type u) [CommRing T] [Algebra R T],
      (H →ₐ[R] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) y)
    (hE : ∀ (T T' : Type u) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
      (a : T →ₐ[R] T') (φ : H →ₐ[R] T),
      (E T' (a.comp φ)).1 = Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (E T φ).1) :
    ∃ i : Spec (CommRingCat.of H) ≅ Y,
      i.hom ≫ y = Spec.map (CommRingCat.ofHom (algebraMap R H)) ∧
      ∀ (T : Type u) [CommRing T] [Algebra R T] (φ : H →ₐ[R] T),
        (E T φ).1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ i.hom := by sorry
