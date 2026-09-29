-- Prove2me | Theorems.Thm_AlgebraicGeometry_existsUnique_comp_eq_of_isClosedImmersion_of_flat_of_genericFibre_comp_eq
-- name    : AlgebraicGeometry.existsUnique_comp_eq_of_isClosedImmersion_of_flat_of_genericFibre_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/2ba3703f-1d65-5092-a794-50ba6fe6726e
-- title:
--   Flat schemes: factoring through a closed subscheme from the generic fibre
-- statement:
--   Let $R$ be a commutative integral domain and let $K$ be a field equipped with an $R$-algebra structure making it a fraction field of $R$ (both in a fixed universe), and let $X$, $Y$, $Z$ be schemes. Assume given a flat morphism $f \colon X \to \operatorname{Spec} R$, a closed immersion $\iota \colon Z \to Y$, and an arbitrary morphism $\varphi \colon X \to Y$. Write $X_K$ for the fibre product of $f$ with the morphism $\operatorname{Spec} K \to \operatorname{Spec} R$ induced by the structure map $R \to K$, and $\mathrm{pr}_1 \colon X_K \to X$ for its first projection. Assume further that there is a morphism $\psi_K \colon X_K \to Z$ whose composite $\psi_K$ followed by $\iota$ equals $\mathrm{pr}_1$ followed by $\varphi$, i.e. the restriction of $\varphi$ to the generic fibre factors through $Z$. The conclusion is that there exists a unique morphism $\psi \colon X \to Z$ with $\psi$ followed by $\iota$ equal to $\varphi$; that is, $\varphi$ itself factors through the closed subscheme $Z$, uniquely so.
--
--   This is the factorisation form of the schematic density of the generic fibre of a flat scheme over an integral base: a morphism from such a scheme is determined by, and descends from, its behaviour over the fraction field. It is used in the project to compare closed subscheme structures and isomorphisms over an integral base with their generic-fibre counterparts, for instance in identifying ideal sheaves after base change to the fraction field and in the construction of integral models of fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_existsUnique_comp_eq_of_isClosedImmersion_of_flat_of_genericFibre_comp_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.existsUnique_comp_eq_of_isClosedImmersion_of_flat_of_genericFibre_comp_eq
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X Y Z : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f]
    (ι : Z ⟶ Y) [IsClosedImmersion ι] (φ : X ⟶ Y)
    (ψK : pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ⟶ Z)
    (hψK : ψK ≫ ι = pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≫ φ) :
    ∃! ψ : X ⟶ Z, ψ ≫ ι = φ := by sorry
