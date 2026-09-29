-- Prove2me | Theorems.Thm_AlgebraicGeometry_IsPullback_exists_iso_Spec_quotient_comp_morphismRestrict_eq
-- name    : AlgebraicGeometry.IsPullback.exists_iso_Spec_quotient_comp_morphismRestrict_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/c2d875bd-17e7-59b2-a34f-bd7424136f45
-- title:
--   Affine charts of a pullback along a nilpotent thickening
-- statement:
--   Let $\pi \colon T' \to T$ be a homomorphism of commutative rings which is surjective and whose kernel $K = \ker \pi$ is nilpotent as an ideal (some power of $K$ is the zero ideal). Let $P$ and $P_0$ be schemes, $p \colon P \to \operatorname{Spec} T'$ and $p_0 \colon P_0 \to \operatorname{Spec} T$ morphisms, and $G \colon P_0 \to P$ a morphism such that the square with top edge $G$, left edge $p_0$, right edge $p$ and bottom edge $\operatorname{Spec}\pi$ is a pullback square. Let $D$ be an open subset of $P$ which is affine, and equip $C = \Gamma(P, D)$ with the $T'$-algebra structure whose structure map is the inverse of the $\Gamma$–$\operatorname{Spec}$ adjunction isomorphism for $T'$ followed by the component $p.\mathrm{appLE}\ \top\ D$ of $p$ on sections. The assertion is twofold: first, the ideal $K \cdot C$, image of $K$ under $T' \to C$, is nilpotent; second, there exists an isomorphism of schemes $\varepsilon \colon \operatorname{Spec}(C/K\cdot C) \cong G^{-1}(D)$ such that $\varepsilon$ followed by the restricted morphism $G \mid_D \colon G^{-1}(D) \to D$ followed by the isomorphism $D \cong \operatorname{Spec} C$ of the affine open $D$ with the spectrum of its sections equals $\operatorname{Spec}$ of the quotient map $C \to C/K\cdot C$.
--
--   This identifies, chart by chart, the closed subscheme $P_0 \subseteq P$ cut out by a nilpotent ideal of the base: over an affine open $D = \operatorname{Spec} C$ of $P$ the fibre $G^{-1}(D)$ is $\operatorname{Spec}(C/K\cdot C)$, compatibly with the restriction of $G$. It serves the gluing arguments for deformation-theoretic thickenings, and is used by the comparison results for affine open covers that build global data from agreeing charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_IsPullback_exists_iso_Spec_quotient_comp_morphismRestrict_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.IsPullback.exists_iso_Spec_quotient_comp_morphismRestrict_eq
    {T' T : Type u} [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    {P P₀ : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of T')) (p₀ : P₀ ⟶ Spec (CommRingCat.of T))
    (G : P₀ ⟶ P) (hG : IsPullback G p₀ p (Spec.map (CommRingCat.ofHom π)))
    (D : P.Opens) (hD : IsAffineOpen D) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom p D
    IsNilpotent ((RingHom.ker π).map (algebraMap T' Γ(P, D))) ∧
    ∃ ε : Spec (CommRingCat.of (Γ(P, D) ⧸ (RingHom.ker π).map (algebraMap T' Γ(P, D)))) ≅ ↑(G ⁻¹ᵁ D),
      ε.hom ≫ G ∣_ D ≫ hD.isoSpec.hom =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(P, D))))) := by sorry
