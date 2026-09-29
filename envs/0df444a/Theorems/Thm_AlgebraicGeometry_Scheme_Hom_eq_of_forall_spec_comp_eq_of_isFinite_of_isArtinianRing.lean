-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Hom_eq_of_forall_spec_comp_eq_of_isFinite_of_isArtinianRing
-- name    : AlgebraicGeometry.Scheme.Hom.eq_of_forall_spec_comp_eq_of_isFinite_of_isArtinianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/f57a9f34-1ef5-5adc-8c24-1a3631551456
-- title:
--   Finite schemes over Artinian rings: Artinian local points are jointly epimorphic
-- statement:
--   Let $T$ be a commutative ring which is Artinian, let $Z$ and $Y$ be schemes, and let $p : Z \to \operatorname{Spec} T$ be a morphism of schemes which is finite (the property `IsFinite`, assumed as an instance on $p$). Let $g, h : Z \to Y$ be two morphisms of schemes. Assume that for every commutative ring $B$ which is Artinian and local, and every morphism $z : \operatorname{Spec} B \to Z$, the two composites agree: $z$ followed by $g$ equals $z$ followed by $h$, i.e. $g \circ z = h \circ z$. The conclusion is that $g = h$. In other words, the family of all morphisms into $Z$ from spectra of Artinian local rings is jointly epimorphic, provided $Z$ admits a finite morphism to the spectrum of an Artinian ring. The morphism $p$ enters only through the hypothesis that it exists and is finite; no compatibility between $p$, $g$ and $h$ is required.
--
--   This is the point-by-point rigidity statement for a scheme finite over an Artinian base: such a $Z$ is a finite disjoint union of spectra of Artinian local rings, so morphisms out of $Z$ are determined by their restrictions to Artinian local points. It is used in the construction of the scheme-theoretic $n$-fold multiplication map on a Weierstrass curve, in [`WeierstrassCurve.DrinfeldGlobal.comp_schemeNsmul_eq_one_of_comp_eq_one_of_zChart_pow_originChart_pow`](thm.html#WeierstrassCurve.DrinfeldGlobal.comp_schemeNsmul_eq_one_of_comp_eq_one_of_zChart_pow_originChart_pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Hom_eq_of_forall_spec_comp_eq_of_isFinite_of_isArtinianRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory

theorem AlgebraicGeometry.Scheme.Hom.eq_of_forall_spec_comp_eq_of_isFinite_of_isArtinianRing
    {T : Type} [CommRing T] [IsArtinianRing T] {Z Y : Scheme} (p : Z ⟶ Spec (CommRingCat.of T)) [IsFinite p]
    (g h : Z ⟶ Y)
    (H : ∀ (B : Type) [CommRing B] [IsArtinianRing B] [IsLocalRing B] (z : Spec (CommRingCat.of B) ⟶ Z), z ≫ g = z ≫ h) :
    g = h := by sorry
