-- Prove2me | Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_specMap_subtype_comp_eq
-- name    : AlgebraicGeometry.IsClosedImmersion.existsUnique_comp_eq_of_specMap_subtype_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/72fd876d-8460-5696-a608-885943db1111
-- title:
--   Integral points factor through closed subschemes
-- statement:
--   Let $\Omega$ be a field (in a fixed universe) and let $O\subseteq\Omega$ be a subring. Let $\iota : Z \to Y$ be a morphism of schemes which is a closed immersion, and let $z : \operatorname{Spec} O \to Y$ be a morphism, where $\operatorname{Spec} O$ denotes the spectrum of the commutative ring underlying $O$. Suppose given a morphism $\psi : \operatorname{Spec}\Omega \to Z$ such that $\psi$ followed by $\iota$ equals $\operatorname{Spec}$ of the inclusion $O \hookrightarrow \Omega$ followed by $z$; that is, the $\Omega$-point of $Y$ obtained by restricting $z$ along $O \hookrightarrow \Omega$ factors through $Z$ via $\psi$. Then there is a unique morphism $\chi : \operatorname{Spec} O \to Z$ with $\chi$ followed by $\iota$ equal to $z$. Note that the conclusion asserts unique existence of a factorisation of $z$ through the closed subscheme $Z$, with no compatibility between $\chi$ and the given $\psi$ being part of the assertion.
--
--   This is the standard statement that a point of $Y$ with values in a subring $O$ of a field $\Omega$ lands in a closed subscheme as soon as its associated $\Omega$-valued point does, the schematic image of $\operatorname{Spec} O$ being controlled by its generic point. It is used in the study of points on the modular curve treated in the project, in the argument that a point whose projection vanishes and whose normalised free part is $q$-divisible is trivial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_specMap_subtype_comp_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.IsClosedImmersion.existsUnique_comp_eq_of_specMap_subtype_comp_eq
    {Ω : Type u} [Field Ω] (O : Subring Ω)
    {Y Z : Scheme.{u}} (ι : Z ⟶ Y) [IsClosedImmersion ι] (z : Spec (CommRingCat.of ↥O) ⟶ Y)
    (ψ : Spec (CommRingCat.of Ω) ⟶ Z) (hψ : ψ ≫ ι = Spec.map (CommRingCat.ofHom O.subtype) ≫ z) :
    ∃! χ : Spec (CommRingCat.of ↥O) ⟶ Z, χ ≫ ι = z := by sorry
