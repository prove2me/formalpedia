-- Prove2me | Theorems.Thm_AlgebraicGeometry_existsUnique_section_comp_eq_of_isFinite_of_isAlgClosed
-- name    : AlgebraicGeometry.existsUnique_section_comp_eq_of_isFinite_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/8ea938b2-0189-5a87-b688-6b473d0d80a3
-- title:
--   k-points of a finite κ-scheme descend uniquely to κ-points
-- statement:
--   Let $\kappa$ be an algebraically closed field and $k$ a field, both in a fixed universe, and let $j : \kappa \to k$ be a ring homomorphism. Let $Z$ be a scheme and $g : Z \to \operatorname{Spec}\kappa$ a morphism which is finite. Let $x : \operatorname{Spec} k \to Z$ be a morphism whose composite $x$ followed by $g$ equals $\operatorname{Spec}(j)$, the morphism $\operatorname{Spec} k \to \operatorname{Spec}\kappa$ induced by $j$. The assertion is that there is exactly one morphism $z : \operatorname{Spec}\kappa \to Z$ such that $z$ followed by $g$ is the identity of $\operatorname{Spec}\kappa$ and such that $\operatorname{Spec}(j)$ followed by $z$ equals $x$; that is, the given $k$-point of $Z$ over $\operatorname{Spec}(j)$ factors through a section of $g$, and that section is unique with these two properties. No reducedness or separability hypothesis on $Z$ enters.
--
--   This is the standard statement that for a finite scheme over an algebraically closed field $\kappa$, points with values in an extension field $k$ of $\kappa$ are induced by $\kappa$-rational points, uniquely so. It is used in the construction of fake elliptic curves for the Čerednik–Drinfel'd setting, in [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_zmod_prod_equiv_factorsThrough_of_isPullback_valuationSubring`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_zmod_prod_equiv_factorsThrough_of_isPullback_valuationSubring).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_existsUnique_section_comp_eq_of_isFinite_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.existsUnique_section_comp_eq_of_isFinite_of_isAlgClosed
    {κ : Type u} [Field κ] [IsAlgClosed κ] {k : Type u} [Field k] (j : κ →+* k)
    {Z : Scheme.{u}} (g : Z ⟶ Spec (CommRingCat.of κ)) [IsFinite g]
    (x : Spec (CommRingCat.of k) ⟶ Z) (hx : x ≫ g = Spec.map (CommRingCat.ofHom j)) :
    ∃! z : Spec (CommRingCat.of κ) ⟶ Z, z ≫ g = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom j) ≫ z = x := by sorry
