-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_section_comp_eq_of_finite_flat_valuationSubring
-- name    : AlgebraicGeometry.exists_section_comp_eq_of_finite_flat_valuationSubring
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.96328+00:00
-- url     : https://prove2.me/theorems/51da2bb5-5710-5832-91f7-efa19921167b
-- title:
--   Lifting residue-field points to sections over a valuation ring
-- statement:
--   Let $L$ be an algebraically closed field and let $\mathcal{O} \subseteq L$ be a valuation subring; as a valuation subring of a field, $\mathcal{O}$ is a local ring, with residue field $k = \mathcal{O}/\mathfrak{m}_{\mathcal{O}}$ and residue homomorphism $\mathcal{O} \to k$. Let $Z$ be a scheme and let $f : Z \to \operatorname{Spec} \mathcal{O}$ be a morphism of schemes that is both finite and flat. Suppose given a morphism $\bar z : \operatorname{Spec} k \to Z$ lying over the closed point of $\operatorname{Spec}\mathcal{O}$, in the precise sense that $f \circ \bar z$ equals the morphism $\operatorname{Spec} k \to \operatorname{Spec} \mathcal{O}$ induced by the residue homomorphism. The conclusion asserts the existence of a morphism $z : \operatorname{Spec} \mathcal{O} \to Z$ which is simultaneously a section of $f$, i.e. $f \circ z$ is the identity of $\operatorname{Spec}\mathcal{O}$, and a lift of $\bar z$, i.e. the composite of $\operatorname{Spec} k \to \operatorname{Spec}\mathcal{O}$ (induced by the residue map) with $z$ equals $\bar z$. No uniqueness is claimed.
--
--   This is the statement that a finite flat scheme over the valuation ring of an algebraically closed field has the property that every point of its special fibre with values in the residue field is the reduction of an $\mathcal{O}$-valued point, hence of a point of the generic fibre. It is used in the Čerednik–Drinfeld part of the argument, where $Z$ is the scheme of extra level structures (a finite flat group-scheme-like object over the valuation ring of $\overline{\mathbb{Q}}$) attached to a fake elliptic curve, to identify residue-field points of the reduction with reductions of characteristic-zero points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_section_comp_eq_of_finite_flat_valuationSubring.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_section_comp_eq_of_finite_flat_valuationSubring
    {L : Type} [Field L] [IsAlgClosed L] (O : ValuationSubring L)
    {Z : Scheme.{0}} (f : Z ⟶ Spec (CommRingCat.of ↥O)) [IsFinite f] [Flat f]
    (zbar : Spec (CommRingCat.of (IsLocalRing.ResidueField ↥O)) ⟶ Z)
    (hzbar : zbar ≫ f = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O))) :
    ∃ z : Spec (CommRingCat.of ↥O) ⟶ Z, z ≫ f = 𝟙 _ ∧
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥O)) ≫ z = zbar := by sorry
