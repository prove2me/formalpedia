-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_section_comp_eq_of_exists_specMap_comp_eq_of_isLocalHom
-- name    : AlgebraicGeometry.Scheme.exists_section_comp_eq_of_exists_specMap_comp_eq_of_isLocalHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/7a33cfae-2b07-583c-9af0-3340e23bdc2a
-- title:
--   Valuative extension of a K-point via a dominating local ring
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K$ (a field $K$ with an $R$-algebra structure making it the fraction ring of $R$), and let $f\colon X \to \operatorname{Spec} R$ be a morphism of schemes that is separated, locally of finite type and quasi-compact. Let $x\colon \operatorname{Spec} K \to X$ be a morphism with $x$ followed by $f$ equal to the map $\operatorname{Spec} K \to \operatorname{Spec} R$ induced by $R \to K$, i.e. a $K$-point of $X$ over $R$. Suppose further given a local ring $R'$ with an $R$-algebra structure whose structure map $R \to R'$ is a local homomorphism, a field $K'$ carrying both an $R'$-algebra and a $K$-algebra structure, and a morphism $y\colon \operatorname{Spec} R' \to X$ with $y$ followed by $f$ equal to the map induced by $R \to R'$, such that the two composites $\operatorname{Spec} K' \to \operatorname{Spec} K \xrightarrow{x} X$ and $\operatorname{Spec} K' \to \operatorname{Spec} R' \xrightarrow{y} X$ (induced by $K \to K'$ and $R' \to K'$ respectively) agree. Then there exists $s\colon \operatorname{Spec} R \to X$ with $s$ followed by $f$ the identity of $\operatorname{Spec} R$, and with the map $\operatorname{Spec} K \to \operatorname{Spec} R$ followed by $s$ equal to $x$; that is, $x$ extends to a section of $f$ over $R$.
--
--   This is a form of the valuative criterion for extending points over a discrete valuation ring: a $K$-point that already extends over some local ring dominating $R$ (for instance a valuation ring of a larger field, or a strict henselisation) extends over $R$ itself, provided $f$ is separated, locally of finite type and quasi-compact. It is used in the construction of Néron-model-type objects attached to modular curves, where it supplies the descent direction of the comparison between points over $R$ and points over a dominating local ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_section_comp_eq_of_exists_specMap_comp_eq_of_isLocalHom.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.exists_section_comp_eq_of_exists_specMap_comp_eq_of_isLocalHom
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (x : Spec (CommRingCat.of K) ⟶ X) (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R K)))

    (R' : Type u) [CommRing R'] [IsLocalRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')]
    (K' : Type u) [Field K'] [Algebra R' K'] [Algebra K K']
    (y : Spec (CommRingCat.of R') ⟶ X) (hy : y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')))
    (hxy : Spec.map (CommRingCat.ofHom (algebraMap K K')) ≫ x = Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫ y) :
    ∃ s : Spec (CommRingCat.of R) ⟶ X, s ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s = x := by sorry
