-- Prove2me | Theorems.Thm_AlgebraicGeometry_existsUnique_section_comp_eq_of_universallyClosed_of_isSeparated
-- name    : AlgebraicGeometry.existsUnique_section_comp_eq_of_universallyClosed_of_isSeparated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/1e5345e8-af5e-5a7c-9b86-350544bbdd8d
-- title:
--   Unique extension of a K-point to a section over a valuation ring
-- statement:
--   Let $R$ be a commutative ring which is a domain and a valuation ring, and let $K$ be a field that is an $R$-algebra realised as the fraction field of $R$ (both in the same universe). Let $X$ be a scheme and let $f \colon X \to \operatorname{Spec} R$ be a morphism which is universally closed and separated, the latter in Mathlib's sense of `IsSeparated` for a morphism. Let $x \colon \operatorname{Spec} K \to X$ be a morphism whose composite with $f$ equals the morphism $\operatorname{Spec} K \to \operatorname{Spec} R$ induced by the structure map $R \to K$. The conclusion is that there is exactly one morphism $\sigma \colon \operatorname{Spec} R \to X$ such that $\sigma$ followed by $f$ is the identity of $\operatorname{Spec} R$, and the morphism $\operatorname{Spec} K \to \operatorname{Spec} R$ induced by $R \to K$ followed by $\sigma$ equals $x$; uniqueness is asserted in the strong form of `∃!`, i.e. any morphism satisfying both conditions coincides with it.
--
--   This is the valuative criterion of properness in the form used to produce sections: a point of the generic fibre of a universally closed separated $\operatorname{Spec} R$-scheme extends uniquely over the valuation ring, the hypotheses being exactly the two halves of properness that are needed (existence from universal closedness, uniqueness from separatedness), with no finite-type or quasi-compactness assumption imposed by hand. It is used downstream to extend $K$-rational points of proper models of modular curves to integral sections, in particular for the cuspidal section and for reduction arguments at a place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_existsUnique_section_comp_eq_of_universallyClosed_of_isSeparated.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.existsUnique_section_comp_eq_of_universallyClosed_of_isSeparated
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [UniversallyClosed f] [IsSeparated f]
    (x : Spec (CommRingCat.of K) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    ∃! σ : Spec (CommRingCat.of R) ⟶ X,
      σ ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ σ = x := by sorry
