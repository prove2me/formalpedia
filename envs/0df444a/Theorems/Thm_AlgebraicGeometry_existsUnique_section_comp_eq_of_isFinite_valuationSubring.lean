-- Prove2me | Theorems.Thm_AlgebraicGeometry_existsUnique_section_comp_eq_of_isFinite_valuationSubring
-- name    : AlgebraicGeometry.existsUnique_section_comp_eq_of_isFinite_valuationSubring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/dd2d0eb1-a754-5ff9-a1e2-86a506c73dad
-- title:
--   Unique extension of L-points to sections over a valuation subring
-- statement:
--   Let $L$ be a field and $O \subseteq L$ a valuation subring, so that $O$ is a valuation ring with fraction field $L$ and the inclusion $O \hookrightarrow L$ induces a morphism $\operatorname{Spec} L \to \operatorname{Spec} O$. Let $Z$ be a scheme and $f : Z \to \operatorname{Spec} O$ a morphism which is finite (`IsFinite f`), and let $x : \operatorname{Spec} L \to Z$ be a morphism whose composite with $f$ is the morphism $\operatorname{Spec} L \to \operatorname{Spec} O$ induced by the inclusion $O \hookrightarrow L$. The assertion is that there is exactly one morphism $z : \operatorname{Spec} O \to Z$ such that $z$ followed by $f$ is the identity of $\operatorname{Spec} O$, i.e. $z$ is a section of $f$, and such that $z$ precomposed with $\operatorname{Spec} L \to \operatorname{Spec} O$ equals $x$; that is, the given $L$-point extends, uniquely, to a section of $f$ over $\operatorname{Spec} O$. Here `∃!` expresses existence and uniqueness of the pair of conditions simultaneously.
--
--   This is the valuative criterion for properness, specialised to a finite morphism over a valuation ring: an $L$-valued point of $Z$ lying over the generic point of $\operatorname{Spec} O$ spreads out to a unique $O$-valued point. It is used in the study of fake elliptic curves over valuation rings, where it produces the section extending a generic-fibre point along a finite morphism, in [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_zmod_prod_equiv_factorsThrough_of_isPullback_valuationSubring`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_zmod_prod_equiv_factorsThrough_of_isPullback_valuationSubring).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_existsUnique_section_comp_eq_of_isFinite_valuationSubring.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.existsUnique_section_comp_eq_of_isFinite_valuationSubring
    {L : Type u} [Field L] (O : ValuationSubring L)
    {Z : Scheme.{u}} (f : Z ⟶ Spec (CommRingCat.of ↥O)) [IsFinite f]
    (x : Spec (CommRingCat.of L) ⟶ Z) (hx : x ≫ f = Spec.map (CommRingCat.ofHom O.subtype)) :
    ∃! z : Spec (CommRingCat.of ↥O) ⟶ Z, z ≫ f = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom O.subtype) ≫ z = x := by sorry
