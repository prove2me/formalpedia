-- Prove2me | Theorems.Thm_AlgebraicGeometry_bijective_comp_sectionsThrough_of_etale_restrict_of_isIso_residueFieldMap
-- name    : AlgebraicGeometry.bijective_comp_sectionsThrough_of_etale_restrict_of_isIso_residueFieldMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/d2dfa111-87db-5c12-abb7-ebb28c8a2623
-- title:
--   Sections through an étale point over a henselian local base
-- statement:
--   Let $A$ be a henselian local ring, and let $fX \colon X \to \operatorname{Spec} A$ and $fY \colon Y \to \operatorname{Spec} A$ be schemes over $\operatorname{Spec} A$, with $g \colon X \to Y$ a morphism satisfying $fY \circ g = fX$. Let $x$ be a point of $X$ and $U$ an open subscheme of $X$ with $x \in U$, such that the composite of the open immersion $U \to X$ with $g$ is étale, and assume that the map $\kappa(g(x)) \to \kappa(x)$ induced by $g$ on residue fields at $x$ is an isomorphism. Consider the set of $A$-sections of $X$ through $x$, namely morphisms $s \colon \operatorname{Spec} A \to X$ with $fX \circ s = \mathrm{id}$ whose underlying map sends the closed point of $\operatorname{Spec} A$ to $x$, and likewise the set of $A$-sections $t$ of $Y$ with $fY \circ t = \mathrm{id}$ sending the closed point to $g(x)$. The assertion is that the map $s \mapsto g \circ s$, which indeed lands in the second set because $fY \circ g \circ s = fX \circ s = \mathrm{id}$ and the underlying map sends the closed point to $g(x)$, is a bijection between these two sets.
--
--   This is the standard rigidity statement for étale morphisms over a henselian local base (EGA IV₄ 18.5.11, 18.5.17): an étale neighbourhood with trivial residue extension at a point $x$ does not change the set of $A$-valued sections reducing to that point. It is applied in the analysis of $A$-points of étale crossing charts on modular curve models, for $A$ a valuation ring of an algebraically closed field, and is cited in the study of the models [`ModularCurve.XHDRModelAtP`](def/ModularCurve_XHDRModelAtP.html#L81) and `ModularCurve.XOneP`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_bijective_comp_sectionsThrough_of_etale_restrict_of_isIso_residueFieldMap.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

theorem AlgebraicGeometry.bijective_comp_sectionsThrough_of_etale_restrict_of_isIso_residueFieldMap {A : Type u} [CommRing A] [HenselianLocalRing A]
    {X Y : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of A)) (fY : Y ⟶ Spec (CommRingCat.of A))
    (g : X ⟶ Y) (hg : g ≫ fY = fX) (x : X)
    (U : X.Opens) (hxU : x ∈ U) [Etale (U.ι ≫ g)]
    (hres : IsIso (g.residueFieldMap x)) :
    Function.Bijective (fun s : {s : Spec (CommRingCat.of A) ⟶ X // s ≫ fX = 𝟙 _ ∧ s.base (IsLocalRing.closedPoint A) = x} =>
      (⟨s.1 ≫ g, ⟨by rw [Category.assoc, hg]; exact s.2.1, by rw [Scheme.Hom.comp_apply, s.2.2]⟩⟩ :
        {t : Spec (CommRingCat.of A) ⟶ Y // t ≫ fY = 𝟙 _ ∧ t.base (IsLocalRing.closedPoint A) = g.base x})) := by sorry
